/*******************************************************************************
 * Copyright (c) 2004-2015, Istvan David, Istvan Rath and Daniel Varro
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 * Istvan David - initial API and implementation
 *******************************************************************************/
package org.eclipse.viatra.cep.core.api.rules;

import org.apache.log4j.Logger;
import org.eclipse.viatra.cep.core.logging.LoggerUtils;
import org.eclipse.viatra.transformation.evm.api.Job;
import org.eclipse.viatra.transformation.evm.api.event.ActivationState;

/**
 * CEP-specific EVM {@link Job}.
 * 
 * @author Istvan David
 * 
 */
public abstract class CepJob<IObservableComplexEventPattern> extends Job<IObservableComplexEventPattern> {
    private Logger logger = LoggerUtils.getInstance().getLogger();

    protected CepJob(ActivationState activationState) {
        super(activationState);
    }

    public Logger getLogger() {
        return logger;
    }
}
