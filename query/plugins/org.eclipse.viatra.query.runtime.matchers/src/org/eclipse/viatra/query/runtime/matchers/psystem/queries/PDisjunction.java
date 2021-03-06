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
package org.eclipse.viatra.query.runtime.matchers.psystem.queries;

import java.util.Set;

import org.eclipse.viatra.query.runtime.matchers.psystem.PBody;

import com.google.common.collect.ImmutableSet;
import com.google.common.collect.ImmutableSet.Builder;
import com.google.common.collect.Iterables;
import com.google.common.collect.Sets;

/**
 * 
 * A disjunction is a set of bodies representing separate conditions. A {@link PQuery} has a single, canonical
 * PDisjunction, that can be replaced using rewriter
 * 
 * @author Zoltan Ujhelyi
 * 
 */
public class PDisjunction {

    private ImmutableSet<PBody> bodies;
    private PQuery query;

    public PDisjunction(Set<PBody> bodies) {
        this(bodies.iterator().next().getPattern(), bodies);
    }

    public PDisjunction(PQuery query, Set<PBody> bodies) {
        super();
        this.query = query;
        final Builder<PBody> builder = ImmutableSet.builder();
        for (PBody body : bodies) {
            body.setContainerDisjunction(this);
            builder.add(body);
        }
        this.bodies = builder.build();
    }

    /**
     * Returns an immutable set of bodies that consists of this disjunction
     * 
     * @return the bodies
     */
    public Set<PBody> getBodies() {
        return bodies;
    }

    /**
     * Returns the corresponding query specification. May be null if not set.
     */
    public PQuery getQuery() {
        return query;
    }

    /**
     * Returns all queries directly referred in the constraints. They are all required to evaluate this query
     * 
     * @return a non-null, but possibly empty list of query definitions
     */
    public Set<PQuery> getDirectReferredQueries() {
        Iterable<PQuery> queries = Iterables.concat(Iterables.transform(this.getBodies(),
                PQueries.directlyReferencedQueriesFunction()));
        return Sets.newHashSet(queries);
    }

    /**
     * Returns all queries required to evaluate this query (transitively).
     * 
     * @return a non-null, but possibly empty list of query definitions
     */
    public Set<PQuery> getAllReferredQueries() {
        Set<PQuery> processedQueries = Sets.newHashSet(this.getQuery());
        Set<PQuery> foundQueries = getDirectReferredQueries();
        Set<PQuery> newQueries = Sets.newHashSet(foundQueries);
    
        while(!processedQueries.containsAll(newQueries)) {
            PQuery query = newQueries.iterator().next();
            processedQueries.add(query);
            newQueries.remove(query);
            Set<PQuery> referred = query.getDirectReferredQueries();
            referred.removeAll(processedQueries);
            foundQueries.addAll(referred);
            newQueries.addAll(referred);
        }
        return foundQueries;
    }
    
    /**
     * Decides whether a disjunction is mutable. A disjunction is mutable if all its contained bodies are mutable.
     * 
     */
    public boolean isMutable() {
        for (PBody body : bodies) {
            if (!body.isMutable()) {
                return false;
            }
        }
        return true;
    }
}
