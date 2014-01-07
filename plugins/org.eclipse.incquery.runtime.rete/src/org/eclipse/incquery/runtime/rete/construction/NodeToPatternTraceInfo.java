/*******************************************************************************
 * Copyright (c) 2010-2013, Bergmann Gabor, Istvan Rath and Daniel Varro
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *   Bergmann Gabor - initial API and implementation
 *******************************************************************************/
package org.eclipse.incquery.runtime.rete.construction;

import org.eclipse.incquery.runtime.matchers.psystem.PQuery;
import org.eclipse.incquery.runtime.rete.network.Node.TraceInfo.PatternTraceInfo;

/**
 * @author Bergmann Gabor
 *
 */
public class NodeToPatternTraceInfo implements PatternTraceInfo {
    PQuery pattern;

    /**
     * @param pattern
     */
    public NodeToPatternTraceInfo(PQuery pattern) {
        super();
        this.pattern = pattern;
    }

    @Override
    public boolean propagateToIndexerParent() {
        return true;
    }

    @Override
    public boolean propagateFromIndexerToSupplierParent() {
        return true;
    }

    @Override
    public boolean propagateFromStandardNodeToSupplierParent() {
        return true;
    }

    @Override
    public boolean propagateToProductionNodeParentAlso() {
        return false;
    }

    @Override
    public String getPatternName() {
        if (pattern != null)
            return pattern.getFullyQualifiedName();
        else
            return "";
    }

    @Override
    public String toString() {
        return "->" + getPatternName();
    }

}
