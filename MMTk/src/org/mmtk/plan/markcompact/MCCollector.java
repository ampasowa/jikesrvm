/*
 *  This file is part of the Jikes RVM project (http://jikesrvm.org).
 *
 *  This file is licensed to You under the Eclipse Public License (EPL);
 *  You may not use this file except in compliance with the License. You
 *  may obtain a copy of the License at
 *
 *      http://www.opensource.org/licenses/eclipse-1.0.php
 *
 *  See the COPYRIGHT.txt file distributed with this work for information
 *  regarding copyright ownership.
 */
package org.mmtk.plan.markcompact;

import org.mmtk.plan.*;
import org.mmtk.policy.MarkCompactCollector;

import org.mmtk.vm.VM;

import org.vmmagic.pragma.*;

/**
 * This class implements <i>per-collector thread</i> behavior
 * and state for the <i>MC</i> plan, which implements a full-heap
 * mark-compact collector.<p>
 *
 * Specifically, this class defines <i>MC</i> collection behavior
 * (through <code>trace</code> and the <code>collectionPhase</code>
 * method), and collection-time allocation.<p>
 *
 * @see MC for an overview of the mark-compact algorithm.<p>
 * @see MCMutator
 * @see StopTheWorldCollector
 * @see CollectorContext
 */
@Uninterruptible
public class MCCollector extends StopTheWorldCollector {

  private static final boolean TRACE_MARK = false;
  private static final boolean TRACE_FORWARD = true;

  /****************************************************************************
   * Instance fields
   */

  /**
   *
   */
  private final MCMarkTraceLocal markTrace;
  private final MCForwardTraceLocal forwardTrace;
  private final MarkCompactCollector mc;
  private boolean currentTrace;

  /****************************************************************************
   *
   * Initialization
   */

  /**
   * Constructor
   */
  public MCCollector() {
    markTrace = new MCMarkTraceLocal(global().markTrace);
    forwardTrace = new MCForwardTraceLocal(global().forwardTrace);
    mc = new MarkCompactCollector(MC.mcSpace);
  }

  /****************************************************************************
   *
   * Collection
   */

  /**
   * {@inheritDoc}
   */
  @Override
  @Inline
  public final void collectionPhase(short phaseId, boolean primary) {
    if (phaseId == MC.PREPARE) {
      currentTrace = TRACE_MARK;
      super.collectionPhase(phaseId, primary);
      markTrace.prepare();
      return;
    }

    if (phaseId == MC.CLOSURE) {
      markTrace.completeTrace();
      return;
    }

    if (phaseId == MC.CALCULATE_FP) {
      mc.createOffsetTable();
      mc.calculateForwardingPointers();
      return;
    }

    if (phaseId == MC.COMPACT) {
      mc.compact();
      return;
    }

    if (phaseId == MC.RELEASE) {
      markTrace.release();
      super.collectionPhase(phaseId, primary);
      return;
    }

    if (phaseId == MC.PREPARE_FORWARD) {
      currentTrace = TRACE_FORWARD;
      super.collectionPhase(MC.PREPARE, primary);
      forwardTrace.prepare();
      return;
    }

    if (phaseId == MC.FORWARD_CLOSURE) {
      forwardTrace.completeTrace();
      return;
    }

    if (phaseId == MC.RELEASE_FORWARD) {
      forwardTrace.release();
      super.collectionPhase(MC.RELEASE, primary);
      return;
    }

    super.collectionPhase(phaseId, primary);
  }

  /****************************************************************************
   *
   * Miscellaneous
   */

  /**
   * {@inheritDoc}
   */
  @Override
  public final TraceLocal getCurrentTrace() {
    if (currentTrace == TRACE_MARK) {
      return markTrace;
    }
    return forwardTrace;
  }

  /** @return The active global plan as an <code>MC</code> instance. */
  @Inline
  private static MC global() {
    return (MC) VM.activePlan.global();
  }
}
