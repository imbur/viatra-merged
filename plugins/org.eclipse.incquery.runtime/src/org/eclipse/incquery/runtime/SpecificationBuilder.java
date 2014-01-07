/*******************************************************************************
 * Copyright (c) 2010-2014, Zoltan Ujhelyi, Istvan Rath and Daniel Varro
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *   Zoltan Ujhelyi - initial API and implementation
 *******************************************************************************/
package org.eclipse.incquery.runtime;

import java.util.Collection;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import org.apache.log4j.Logger;
import org.eclipse.incquery.patternlanguage.helper.CorePatternLanguageHelper;
import org.eclipse.incquery.patternlanguage.patternLanguage.Annotation;
import org.eclipse.incquery.patternlanguage.patternLanguage.Pattern;
import org.eclipse.incquery.patternlanguage.patternLanguage.PatternBody;
import org.eclipse.incquery.runtime.api.IPatternMatch;
import org.eclipse.incquery.runtime.api.IQuerySpecification;
import org.eclipse.incquery.runtime.api.IncQueryMatcher;
import org.eclipse.incquery.runtime.exception.IncQueryException;
import org.eclipse.incquery.runtime.internal.EMFPatternMatcherContext;
import org.eclipse.incquery.runtime.internal.PatternSanitizer;
import org.eclipse.incquery.runtime.internal.apiimpl.GenericQuerySpecification;
import org.eclipse.incquery.runtime.internal.matcherbuilder.EPMToPBody;
import org.eclipse.incquery.runtime.internal.matcherbuilder.NameToSpecificationMap;
import org.eclipse.incquery.runtime.matchers.IPatternMatcherContext;
import org.eclipse.incquery.runtime.matchers.planning.QueryPlannerException;
import org.eclipse.incquery.runtime.matchers.psystem.InitializablePQuery;
import org.eclipse.incquery.runtime.matchers.psystem.PBody;
import org.eclipse.incquery.runtime.matchers.psystem.PBodyNormalizer;
import org.eclipse.incquery.runtime.matchers.psystem.PQuery;
import org.eclipse.incquery.runtime.matchers.psystem.PQuery.PQueryStatus;
import org.eclipse.incquery.runtime.matchers.psystem.annotations.PAnnotation;

import com.google.common.base.Preconditions;
import com.google.common.base.Predicate;
import com.google.common.collect.Iterables;
import com.google.common.collect.Sets;

/**
 * An instance class to initialize {@link PBody} instances from {@link Pattern} definitions. A single instance of this
 * builder is used during construction, that maintains the mapping between {@link Pattern} and {@link PQuery} objects,
 * and can be initialized with a pre-defined set of mappings.</p>
 *
 * <p>
 * The SpecificationBuilder is stateful: it stores all previously built specifications, allowing further re-use.
 *
 * @author Zoltan Ujhelyi
 *
 */
public class SpecificationBuilder {

    private Logger logger = Logger.getLogger(SpecificationBuilder.class);
    private NameToSpecificationMap patternMap;
    /**
     * This map is used to detect a re-addition of a pattern with a fqn that is used by a previously added pattern.
     */
    private Map<String, Pattern> patternNameMap = new HashMap<String, Pattern>();
    private IPatternMatcherContext context = new EMFPatternMatcherContext(logger);
    private PatternSanitizer sanitizer = new PatternSanitizer(logger);

    /**
     * Initializes a query builder with no previously known query specifications
     */
    public SpecificationBuilder() {
        patternMap = new NameToSpecificationMap();
    }

    /**
     * Sets up a query builder with a predefined set of specifications
     */
    public SpecificationBuilder(IQuerySpecification<?>... specifications) {
        patternMap = new NameToSpecificationMap(specifications);
        processPatternSpecifications();
    }

    /**
     * Sets up a query builder with a predefined collection of specifications
     */
    public SpecificationBuilder(Collection<? extends IQuerySpecification<? extends IncQueryMatcher<? extends IPatternMatch>>> specifications) {
        patternMap = new NameToSpecificationMap(specifications);
        processPatternSpecifications();
    }

    public SpecificationBuilder(NameToSpecificationMap patternMap) {
        this.patternMap = patternMap;
        processPatternSpecifications();
    }

    /**
     * Processes all existing query specifications searching for possible pattern instances, and if found, add it to the {@link #patternNameMap}.
     */
    private void processPatternSpecifications() {
        for (GenericQuerySpecification spec : Iterables.filter(patternMap.values(), GenericQuerySpecification.class)) {
            patternNameMap.put(spec.getFullyQualifiedName(), spec.getPattern());
        }
    }

    /**
     * Creates a new or returns an existing query specification for the pattern. It is expected, that the builder will
     * not be called with different patterns having the same fqn over its entire lifecycle.
     *
     * @param pattern
     * @return
     * @throws IncQueryException
     */
    public IQuerySpecification<? extends IncQueryMatcher<? extends IPatternMatch>> getOrCreateSpecification(Pattern pattern) throws IncQueryException {
        String fqn = CorePatternLanguageHelper.getFullyQualifiedName(pattern);
        Preconditions.checkArgument(!patternNameMap.containsKey(fqn) || pattern.equals(patternNameMap.get(fqn)),
                "This builder already contains a different pattern with the fqn %s of the newly added pattern.", fqn);
        IQuerySpecification<?> specification = getSpecification(pattern);
        if (specification == null) {
            specification = buildSpecification(pattern);
        }
        return specification;
    }

    protected IQuerySpecification<?> buildSpecification(Pattern pattern) throws IncQueryException {
        String fqn = CorePatternLanguageHelper.getFullyQualifiedName(pattern);
        Preconditions.checkArgument(!patternMap.containsKey(fqn), "Builder already stores query with the name of "
                + fqn);
        if (sanitizer.admit(pattern)) {
            Set<Pattern> newPatterns = Sets.newHashSet(Sets.filter(sanitizer.getAdmittedPatterns(), new Predicate<Pattern>() {

                @Override
                public boolean apply(Pattern pattern) {
                    return !patternMap.containsKey(CorePatternLanguageHelper.getFullyQualifiedName(pattern));
                }
            }));
            // Initializing new query specifications
            for (Pattern newPattern : newPatterns) {
                String patternFqn = CorePatternLanguageHelper.getFullyQualifiedName(newPattern);
                GenericQuerySpecification specification = new GenericQuerySpecification(newPattern, true);
                patternMap.put(patternFqn, specification);
                patternNameMap.put(patternFqn, newPattern);
            }
            // Updating bodies
            for (Pattern newPattern : newPatterns) {
                String patternFqn = CorePatternLanguageHelper.getFullyQualifiedName(newPattern);
                GenericQuerySpecification specification = (GenericQuerySpecification) patternMap.get(patternFqn);
                EPMToPBody converter = new EPMToPBody(newPattern, specification, context, patternMap);
                buildAnnotations(newPattern, specification, converter);
                buildBodies(newPattern, specification, converter);
            }
        } else {
            //TODO currently sanitizer logs errors to output - but erroneous specifications are created here
            for (Pattern rejectedPattern : sanitizer.getRejectedPatterns()) {
                String patternFqn = CorePatternLanguageHelper.getFullyQualifiedName(rejectedPattern);
                if (!patternMap.containsKey(patternFqn)) {
                    GenericQuerySpecification rejected = new GenericQuerySpecification(rejectedPattern, true);
                    rejected.setStatus(PQueryStatus.ERROR);
                    patternMap.put(patternFqn, rejected);
                    patternNameMap.put(patternFqn, rejectedPattern);
                }
            }
        }
        return patternMap.get(fqn);
    }

    protected void buildAnnotations(Pattern pattern, InitializablePQuery query, EPMToPBody converter) throws IncQueryException {
        for (Annotation annotation : pattern.getAnnotations()) {
            PAnnotation pAnnotation = converter.toPAnnotation(annotation);
            query.addAnnotation(pAnnotation);
        }
    }

    public Set<PBody> buildBodies(Pattern pattern, InitializablePQuery query) throws IncQueryException {
        return buildBodies(pattern, query, new EPMToPBody(pattern, query, context, patternMap));
    }

    protected Set<PBody> buildBodies(Pattern pattern, InitializablePQuery query, EPMToPBody converter) throws IncQueryException {
        Set<PBody> bodies = getBodies(pattern, query, converter);
        query.initializeBodies(bodies);
        return bodies;
    }

    public Set<PBody> getBodies(Pattern pattern, PQuery query) throws IncQueryException {
        return getBodies(pattern, query, new EPMToPBody(pattern, query, context, patternMap));
    }

    public Set<PBody> getBodies(Pattern pattern, PQuery query, EPMToPBody converter) throws IncQueryException {
        try {
            Set<PBody> bodies = Sets.newHashSet();
            for (PatternBody body : pattern.getBodies()) {
                PBody pBody = converter.toPBody(body);
                bodies.add(PBodyNormalizer.normalizeBody(pBody, context));
            }
            return bodies;
        } catch (QueryPlannerException e) {
            throw new IncQueryException(e);
        }
    }

    public IQuerySpecification<?> getSpecification(Pattern pattern) {
        String fqn = CorePatternLanguageHelper.getFullyQualifiedName(pattern);
        return getSpecification(fqn);
    }

    public IQuerySpecification<?> getSpecification(String fqn) {
        return patternMap.get(fqn);
    }

}
