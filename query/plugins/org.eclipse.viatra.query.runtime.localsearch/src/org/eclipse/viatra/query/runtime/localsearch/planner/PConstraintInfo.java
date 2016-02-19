/** 
 * Copyright (c) 2010-2016, Marton Bur, Zoltan Ujhelyi, Akos Horvath, Istvan Rath and Daniel Varro
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 * Contributors:
 * Marton Bur - initial API and implementation
 */
package org.eclipse.viatra.query.runtime.localsearch.planner;

import java.util.Arrays;
import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.eclipse.viatra.query.runtime.matchers.context.IInputKey;
import org.eclipse.viatra.query.runtime.matchers.context.IQueryMetaContext;
import org.eclipse.viatra.query.runtime.matchers.context.IQueryRuntimeContext;
import org.eclipse.viatra.query.runtime.matchers.context.InputKeyImplication;
import org.eclipse.viatra.query.runtime.matchers.psystem.PBody;
import org.eclipse.viatra.query.runtime.matchers.psystem.PConstraint;
import org.eclipse.viatra.query.runtime.matchers.psystem.PVariable;
import org.eclipse.viatra.query.runtime.matchers.psystem.basicdeferred.ExportedParameter;
import org.eclipse.viatra.query.runtime.matchers.psystem.basicenumerables.ConstantValue;
import org.eclipse.viatra.query.runtime.matchers.psystem.basicenumerables.TypeConstraint;

import com.google.common.collect.Maps;
import com.google.common.collect.Sets;

/** 
 * Wraps a PConstraint together with information required for the planner. Currently contains information about the expected binding state of
 * the affected variables also called application condition, and the cost of the enforcement, based on the meta and/or the runtime context.
 *  
 * @author Marton Bur
 */
public class PConstraintInfo {

    private PConstraint constraint;
    private Set<PVariable> boundMaskVariables;
    private Set<PVariable> freeMaskVariables;
    private Set<PConstraintInfo> sameWithDifferentBindings;
    private IQueryRuntimeContext runtimeContext;

    private static float MAX_COST = 250.0f;
    private static float DEFAULT_COST = MAX_COST-100.0f;
    private float cost;

    private static Map<IInputKey, Integer> modelStatisticCache = Maps.newHashMap();
    
    public static void flushModelStatistics(){
        modelStatisticCache = Maps.newHashMap();
    }

    public static int getModelStatistic(IInputKey supplierKey, IQueryRuntimeContext runtimeContext){
        
        if(modelStatisticCache.get(supplierKey)!=null){
            return modelStatisticCache.get(supplierKey);
        }
        
        int count = runtimeContext.countTuples(supplierKey, null);
        
        modelStatisticCache.put(supplierKey, count);
        return count;
    }

    /** 
     * Instantiates the wrapper
     * @param constraintfor which the information is added and stored
     * @param boundMaskVariablesthe bound variables in the operation mask
     * @param freeMaskVariablesthe free variables in the operation mask
     * @param sameWithDifferentBindingsduring the planning process, multiple operation adornments are considered for a constraint, so that it
     * is represented by multiple plan infos. This parameter contains all plan infos that are for the same
     * constraint, but with different adornment
     * @param runtimeContextthe runtime query context
     */
    public PConstraintInfo(PConstraint constraint, Set<PVariable> boundMaskVariables, Set<PVariable> freeMaskVariables,
        Set<PConstraintInfo> sameWithDifferentBindings, IQueryRuntimeContext runtimeContext) {
        this.constraint = constraint;
        this.boundMaskVariables = boundMaskVariables;
        this.freeMaskVariables = freeMaskVariables;
        this.sameWithDifferentBindings = sameWithDifferentBindings;
        this.runtimeContext = runtimeContext;

        // Calculate cost of the constraint based on its type
        // Dispatch in java by type explicitly
        if (constraint instanceof ExportedParameter) {
            calculateCost((ExportedParameter) constraint);
            return;
        } else if (constraint instanceof ConstantValue) {
            calculateCost((ConstantValue) constraint);
            return;
        } else if (constraint instanceof TypeConstraint) {
            calculateCost((TypeConstraint) constraint);
            return;
        } else if (constraint != null) {
            calculateCost(constraint);
            return;
        } else {
            throw new IllegalArgumentException(
                    "Unhandled parameter types: " + Arrays.<Object> asList(constraint).toString());
        }
        
    }

    protected void calculateCost(ConstantValue constant) {
        cost = 1.0f;
        return;
    }

    protected void calculateCost(TypeConstraint typeConstraint) {

        IInputKey supplierKey = ((TypeConstraint)constraint).getSupplierKey();
        long arity = supplierKey.getArity();
        if (arity == 1) {
            // unary constraint
            calculateUnaryConstraintCost(supplierKey);
        } else if (arity == 2) {
            // binary constraint
            long edgeCount = getModelStatistic(supplierKey, runtimeContext);
            PVariable srcVariable = (PVariable)((TypeConstraint)constraint).getVariablesTuple().get(0);
            PVariable dstVariable = (PVariable)((TypeConstraint)constraint).getVariablesTuple().get(1);
            boolean isInverse = false;
            // Check if inverse navigation is needed along the edge
            if (freeMaskVariables.contains(srcVariable) && boundMaskVariables.contains(dstVariable)) {
                isInverse = true;
            }
            if (freeMaskVariables.contains(srcVariable) || freeMaskVariables.contains(dstVariable)) {
                // This case it is not a check
                // at least one of the variables are free, so calculate cost based on the meta or/and the runtime context
                calculateBinaryExtendCost(supplierKey, srcVariable, dstVariable, isInverse, edgeCount);
            } else {
                // It is a check operation, both variables are bound
                cost = 1.0f;
            }
        } else {
            // n-ary constraint
            throw new RuntimeException("Cost calculation for arity " +arity+" is not implemented yet");
        }
    }
    
    protected void calculateBinaryExtendCost(IInputKey supplierKey, PVariable srcVariable, PVariable dstVariable, boolean isInverse, long edgeCount) {
        IQueryMetaContext metaContext = runtimeContext.getMetaContext();
        Collection<InputKeyImplication> implications = metaContext.getImplications(supplierKey);
        // TODO prepare for cases when this info is not available - use only metamodel related cost calculation (see TODO at the beginning of the function)
        long srcCount = -1;
        long dstCount = -1;
        // Obtain runtime information
        for (InputKeyImplication implication : implications) {
            List<Integer> impliedIndices = implication.getImpliedIndices();
            if (impliedIndices.size() == 1 && impliedIndices.contains(0)) {
                // Source key implication
                srcCount = getModelStatistic(implication.getImpliedKey(), runtimeContext);
            } else if (impliedIndices.size() == 1 && impliedIndices.contains(1)) {
                // Target key implication
                dstCount = getModelStatistic(implication.getImpliedKey(), runtimeContext);
            }
        
        }
        if (freeMaskVariables.contains(srcVariable) && freeMaskVariables.contains(dstVariable)) {
            cost = dstCount * srcCount;
        } else {
            long srcNodeCount = -1;
            long dstNodeCount = -1;
            if (isInverse) {
                srcNodeCount = dstCount;
                dstNodeCount = srcCount;
            } else {
                srcNodeCount = srcCount;
                dstNodeCount = dstCount;
            }
            
            if (srcNodeCount > -1 && edgeCount > -1) {
                // The end nodes had implied (type) constraint and both nodes and adjacent edges are indexed
                if (srcNodeCount == 0) {
                    cost = 0;
                } else {
                    cost = ((float)edgeCount) / srcNodeCount;
                }
            } else if (srcCount > -1 && dstCount > -1) {
                // Both of the end nodes had implied (type) constraint
                if(srcCount != 0) {
                    cost = dstNodeCount / srcNodeCount;
                } else {
                    // No such element exists in the model, so the traversal will backtrack at this point
                    cost = 1.0f;
                }
            } else {
                // At least one of the end variables had no restricting type information
                // Strategy: try to navigate along many-to-one relations
                Map<Set<PVariable>, Set<PVariable>> functionalDependencies = constraint.getFunctionalDependencies(metaContext);
                Set<PVariable> impliedVariables = functionalDependencies.get(boundMaskVariables);
                if(impliedVariables != null && impliedVariables.containsAll(freeMaskVariables)){
                    cost = 1.0f;
                } else {
                    cost = DEFAULT_COST;
                }
            }
        }
        return;
    }
    
    protected void calculateUnaryConstraintCost(IInputKey supplierKey) {
        PVariable variable = (PVariable)((TypeConstraint)constraint).getVariablesTuple().get(0);
        if (boundMaskVariables.contains(variable)) {
            cost = 0.9f;
        } else {
            cost = getModelStatistic(supplierKey, runtimeContext);
        }
    }

    protected void calculateCost(ExportedParameter exportedParam) {
        cost = MAX_COST;
    }

    /**
     * Default cost calculation strategy
     */
    protected void calculateCost(PConstraint constraint) {
        if (freeMaskVariables.isEmpty()) {
            cost = 1.0f;
        } else {
            cost = DEFAULT_COST;
        }
    }

    PConstraint getConstraint() {
        return constraint;
    }

    Set<PVariable> getFreeVariables() {
        return freeMaskVariables;
    }

    Set<PVariable> getBoundVariables() {
        return boundMaskVariables;
    }

    Set<PConstraintInfo> getSameWithDifferentBindings() {
        return sameWithDifferentBindings;
    }

    public float getCost() {
        return cost;
    }

    PConstraintCategory getCategory(PBody pBody, Set<PVariable> boundVariables) {
        if (Sets.intersection(this.freeMaskVariables, boundVariables).size() > 0) {
            return PConstraintCategory.PAST;
        } else if (Sets.intersection(this.boundMaskVariables, Sets.difference(pBody.getAllVariables(), boundVariables)).
            size() > 0) {
            return PConstraintCategory.FUTURE;
        } else {
            return PConstraintCategory.PRESENT;
        }
    }

    public String toString(){
        
        return String.format("\n") + constraint.toString() + " bound variables: " + boundMaskVariables+ ", cost: "+ String.format("%.2f",cost); 
    }
    

}
