/*******************************************************************************
 * Copyright (c) 2010-2014, Balint Lorand, Zoltan Ujhelyi, Abel Hegedus, Tamas Szabo, Istvan Rath and Daniel Varro
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *   Zoltan Ujhelyi, Abel Hegedus, Tamas Szabo - original initial API and implementation
 *   Balint Lorand - revised API and implementation
 *******************************************************************************/

package org.eclipse.viatra.addon.validation.core.listeners;

import org.eclipse.viatra.addon.validation.core.api.IViolation;

/**
 * Interface for listening for notifications on specific events regarding a constraint.
 * 
 * @author Balint Lorand
 *
 */
public interface ConstraintListener {

    /**
     * Called if a new violation appeared for the constraint on which the listener is registered.
     * 
     * @param violation
     *            The violation which appeared.
     */
    public void violationAppeared(IViolation violation);

    /**
     * Called if a violation disappeared for the constraint on which the listener is registered.
     * 
     * @param violation
     *            The violation which disappeared.
     */
    public void violationDisappeared(IViolation violation);

}
