/*******************************************************************************
 * Copyright (c) 2004-2008 Gabor Bergmann and Daniel Varro
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Gabor Bergmann - initial API and implementation
 *******************************************************************************/

package org.eclipse.viatra.query.runtime.rete.matcher;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Map;

import org.eclipse.viatra.query.runtime.matchers.backend.IQueryBackend;
import org.eclipse.viatra.query.runtime.matchers.backend.IQueryResultProvider;
import org.eclipse.viatra.query.runtime.matchers.backend.IUpdateable;
import org.eclipse.viatra.query.runtime.matchers.context.IQueryRuntimeContext;
import org.eclipse.viatra.query.runtime.matchers.tuple.FlatTuple;
import org.eclipse.viatra.query.runtime.matchers.tuple.Tuple;
import org.eclipse.viatra.query.runtime.matchers.tuple.TupleMask;
import org.eclipse.viatra.query.runtime.matchers.util.CollectionsFactory;
import org.eclipse.viatra.query.runtime.rete.index.Indexer;
import org.eclipse.viatra.query.runtime.rete.network.Node;
import org.eclipse.viatra.query.runtime.rete.network.Production;
import org.eclipse.viatra.query.runtime.rete.network.Receiver;
import org.eclipse.viatra.query.runtime.rete.remote.Address;
import org.eclipse.viatra.query.runtime.rete.single.CallbackNode;
import org.eclipse.viatra.query.runtime.rete.single.TransformerNode;
import org.eclipse.viatra.query.runtime.rete.traceability.RecipeTraceInfo;

/**
 * @author Gabor Bergmann
 *
 */
public class RetePatternMatcher extends TransformerNode implements IQueryResultProvider {

    protected ReteEngine engine;
    protected IQueryRuntimeContext context;
    protected Production productionNode;
    protected RecipeTraceInfo productionNodeTrace;
    protected Map<String, Integer> posMapping;
    protected Map<Object, Receiver> taggedChildren = //new HashMap<Object, Receiver>();
            CollectionsFactory.getMap();
    protected boolean connected = false; // is rete-wise connected to the
                                         // production node?

    /**
     * @param productionNode
     *            a production node that matches this pattern without any parameter bindings
     * @pre: Production must be local to the head container
     */
    public RetePatternMatcher(ReteEngine engine, RecipeTraceInfo productionNodeTrace) {
        super(engine.getReteNet().getHeadContainer());
        this.engine = engine;
        this.context = engine.getRuntimeContext();
        this.productionNodeTrace = productionNodeTrace;
        final Address<? extends Node> productionAddress = reteContainer.getProvisioner().getOrCreateNodeByRecipe(productionNodeTrace);
        if (!reteContainer.isLocal(productionAddress))
        	throw new IllegalArgumentException("@pre: Production must be local to the head container");
		this.productionNode = (Production) reteContainer.resolveLocal(productionAddress);
        this.posMapping = this.productionNode.getPosMapping();
    }

    // /**
    // * @return the productionNode
    // */
    // public Production getProductionNode() {
    // return productionNode;
    // }

    public Tuple matchOneRandomly(Object[] inputMapping, boolean[] fixed) {
        ArrayList<Tuple> allMatches = matchAll(inputMapping, fixed);
        if (allMatches == null || allMatches.isEmpty())
            return null;
        else
            return allMatches.get((int) (Math.random() * allMatches.size()));
    }

    public ArrayList<Tuple> matchAll(Object[] inputMapping, boolean[] fixed) {
        // retrieving the projection
        TupleMask mask = new TupleMask(fixed);
        Tuple inputSignature = mask.transform(new FlatTuple(inputMapping));

        AllMatchFetcher fetcher = new AllMatchFetcher(engine.accessProjection(productionNodeTrace, mask),
        		context.wrapTuple(inputSignature));
        engine.reteNet.waitForReteTermination(fetcher);
        ArrayList<Tuple> unscopedMatches = fetcher.getMatches();

        // checking scopes
        if (unscopedMatches == null)
            return new ArrayList<Tuple>();
        else
            return unscopedMatches;

    }

    public Tuple matchOne(Object[] inputMapping, boolean[] fixed) {
        // retrieving the projection
        TupleMask mask = new TupleMask(fixed);
        Tuple inputSignature = mask.transform(new FlatTuple(inputMapping));

        SingleMatchFetcher fetcher = new SingleMatchFetcher(engine.accessProjection(productionNodeTrace, mask),
        		context.wrapTuple(inputSignature));
        engine.reteNet.waitForReteTermination(fetcher);
        return fetcher.getMatch();
    }

    /**
     * Counts the number of occurrences of the pattern that match inputMapping on positions where fixed is true.
     *
     * @return the number of occurrences
     */
    public int count(Object[] inputMapping, boolean[] fixed) {
        TupleMask mask = new TupleMask(fixed);
        Tuple inputSignature = mask.transform(new FlatTuple(inputMapping));

        CountFetcher fetcher = new CountFetcher(engine.accessProjection(productionNodeTrace, mask),
        		context.wrapTuple(inputSignature));
        engine.reteNet.waitForReteTermination(fetcher);

        return fetcher.getCount();
    }

    /**
     * Connects a new external receiver that will receive update notifications from now on. The receiver will
     * practically connect to the production node, the added value is unwrapping the updates for external use.
     *
     * @param synchronize
     *            if true, the contents of the production node will be inserted into the receiver after the connection
     *            is established.
     */
    public synchronized void connect(Receiver receiver, boolean synchronize) {
        if (!connected) { // connect to the production node as a RETE-child
            reteContainer.connect(productionNode, this);
            connected = true;
        }
        if (synchronize)
            reteContainer.connectAndSynchronize(this, receiver);
        else
            reteContainer.connect(this, receiver);
    }

    /**
     * Connects a new external receiver that will receive update notifications from now on. The receiver will
     * practically connect to the production node, the added value is unwrapping the updates for external use.
     *
     * The external receiver will be disconnectable later based on its tag.
     *
     * @param tag
     *            an identifier to recognize the child node by.
     *
     * @param synchronize
     *            if true, the contents of the production node will be inserted into the receiver after the connection
     *            is established.
     *
     */
    public synchronized void connect(Receiver receiver, Object tag, boolean synchronize) {
        taggedChildren.put(tag, receiver);
        connect(receiver, synchronize);
    }

    /**
     * Disconnects a child node.
     */
    public synchronized void disconnect(Receiver receiver) {
        reteContainer.disconnect(this, receiver);
    }

    /**
     * Disconnects the child node that was connected by specifying the given tag.
     *
     * @return if a child node was found registered with this tag.
     */
    public synchronized boolean disconnectByTag(Object tag) {
        final Receiver receiver = taggedChildren.remove(tag);
        final boolean found = receiver != null;
        if (found)
            disconnect(receiver);
        return found;
    }

    @Override
    protected Tuple transform(Tuple input) {
        return context.unwrapTuple(input);
    }

    abstract class AbstractMatchFetcher implements Runnable {
        Indexer indexer;
        Tuple signature;

        public AbstractMatchFetcher(Indexer indexer, Tuple signature) {
            super();
            this.indexer = indexer;
            this.signature = signature;
        }

        public void run() {
            fetch(indexer.get(signature));
        }

        protected abstract void fetch(Collection<Tuple> matches);

    }

    class AllMatchFetcher extends AbstractMatchFetcher {

        public AllMatchFetcher(Indexer indexer, Tuple signature) {
            super(indexer, signature);
        }

        ArrayList<Tuple> matches = null;

        public ArrayList<Tuple> getMatches() {
            return matches;
        }

        @Override
        protected void fetch(Collection<Tuple> matches) {
            if (matches == null)
                this.matches = null;
            else {
                this.matches = new ArrayList<Tuple>(matches.size());
                int i = 0;
                for (Tuple t : matches)
                    this.matches.add(i++, context.unwrapTuple(t));
            }

        }

    }

    class SingleMatchFetcher extends AbstractMatchFetcher {

        public SingleMatchFetcher(Indexer indexer, Tuple signature) {
            super(indexer, signature);
        }

        Tuple match = null;

        public Tuple getMatch() {
            return match;
        }

        @Override
        protected void fetch(Collection<Tuple> matches) {
            if (matches != null && !matches.isEmpty())
                match = context.unwrapTuple(matches.iterator().next());
        }

        // public void run() {
        // Collection<Tuple> unscopedMatches = indexer.get(signature);
        //
        // // checking scopes
        // if (unscopedMatches != null) {
        // for (Tuple um : /* productionNode */unscopedMatches) {
        // match = inputConnector.unwrapTuple(um);
        // return;
        //
        // // Tuple ps = inputConnector.unwrapTuple(um);
        // // boolean ok = true;
        // // if (!ignoreScope) for (int k = 0; (k < ps.getSize()) && ok; k++) {
        // // if (pcs[k].getParameterMode() == ParameterMode.INPUT) {
        // // // ok = ok && (inputMapping[k]==ps.elements[k]);
        // // // should now be true
        // // } else // ParameterMode.OUTPUT
        // // {
        // // IEntity scopeParent = (IEntity) pcs[k].getParameterScope().getParent();
        // // Integer containmentMode = pcs[k].getParameterScope().getContainmentMode();
        // // if (containmentMode == Scope.BELOW)
        // // ok = ok && ((IModelElement) ps.get(k)).isBelowNamespace(scopeParent);
        // // else
        // // /* case Scope.IN: */
        // // ok = ok && scopeParent.equals(((IModelElement) ps.get(k)).getNamespace());
        // // // note: getNamespace returns null instead of the
        // // // (imaginary) modelspace root entity for top level
        // // // elements;
        // // // this is not a problem here as Scope.IN implies
        // // // scopeParent != root.
        // //
        // // }
        // // }
        // //
        // // if (ok) {
        // // reteMatching = new ReteMatching(ps, posMapping);
        // // return;
        // // }
        // }
        // }
        //
        // }

    }

    class CountFetcher extends AbstractMatchFetcher {

        public CountFetcher(Indexer indexer, Tuple signature) {
            super(indexer, signature);
        }

        int count = 0;

        public int getCount() {
            return count;
        }

        @Override
        protected void fetch(Collection<Tuple> matches) {
            count = matches == null ? 0 : matches.size();
        }

    }

    
    private boolean[] notNull(Object[] parameters) {
        boolean[] notNull = new boolean[parameters.length];
        for (int i = 0; i < parameters.length; ++i)
            notNull[i] = parameters[i] != null;
        return notNull;
    }
    
	@Override
	public int countMatches(Object[] parameters) {
		return count(parameters, notNull(parameters));
	}

	@Override
	public Tuple getOneArbitraryMatch(Object[] parameters) {
		return matchOne(parameters, notNull(parameters));
	}

	@Override
	public Collection<? extends Tuple> getAllMatches(Object[] parameters) {
		return matchAll(parameters, notNull(parameters));
	}
	
	@Override
	public IQueryBackend getQueryBackend() {
		return engine;
	}

	@Override
	public void addUpdateListener(
			final IUpdateable listener,
			final Object listenerTag,
			boolean fireNow) {
		final CallbackNode callbackNode = new CallbackNode(this.reteContainer, listener);
		connect(callbackNode, listenerTag, fireNow);
	}
	
	@Override
	public void removeUpdateListener(Object listenerTag) {
		disconnectByTag(listenerTag);
	}

}
