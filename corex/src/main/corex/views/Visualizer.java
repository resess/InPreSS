package corex.views;

import java.util.HashMap;
import java.util.List;

import org.eclipse.swt.widgets.Display;

import corex.model.PairList;
import corex.separatesnapshots.DiffMatcher;
import microbat.model.trace.Trace;
import microbat.model.trace.TraceNode;
import microbat.model.value.VarValue;
import sav.common.core.Pair;

public class Visualizer {
	public void visualize(final TraceNode observedFaultNode, final TraceNode observedFault_old, final List<TraceNode> new_changes,final List<TraceNode> old_changes, final Trace newTrace, final Trace oldTrace, 
			final PairList pairList, final DiffMatcher diffMatcher, final List<TraceNode> new_trace, final List<TraceNode> old_trace, 
			final List<TraceNode> new_kept, final List<TraceNode> old_kept,
			final HashMap<TraceNode, List<Pair<TraceNode, VarValue>>> new_kept_data_edges, final HashMap<TraceNode, List<Pair<TraceNode, VarValue>>> old_kept_data_edges,
			final HashMap<TraceNode, List<TraceNode>> new_kept_ctl_edges,final HashMap<TraceNode, List<TraceNode>> old_kept_ctl_edges) {

		Display.getDefault().asyncExec(new Runnable() {

			@Override
			public void run() {
				OldTraceView oldView = CorexViews.getOldTraceView();
				oldView.setMainTrace(oldTrace);
				oldView.setMainKeptNodes(old_kept);
				oldView.setObservedFailuredNode(new Pair<TraceNode, String>(observedFault_old,"OLD"));
				oldView.setChangedNodes(old_changes);
				oldView.updateData();
				oldView.setPairList(pairList);
				oldView.setDiffMatcher(diffMatcher);
				oldView.setNewKeptList(new_kept);
				oldView.setOldKeptList(old_kept);
				oldView.setNewTraceList(new_trace);
				oldView.setOldTraceList(old_trace);
				oldView.setOldDataEdges(old_kept_data_edges);
				oldView.setNewDataEdges(new_kept_data_edges);
				oldView.setOldCtlEdges(old_kept_ctl_edges);
				oldView.setNewCtlEdges(new_kept_ctl_edges);
				

				NewTraceView newView = CorexViews.getNewTraceView();
				newView.setMainTrace(newTrace);
				newView.setMainKeptNodes(new_kept);
				newView.setObservedFailuredNode(new Pair<TraceNode, String>(observedFaultNode,"NEW"));
				newView.setChangedNodes(new_changes);
				newView.updateData();
				newView.setPairList(pairList);
				newView.setDiffMatcher(diffMatcher);
				newView.setNewKeptList(new_kept);
				newView.setOldKeptList(old_kept);
				newView.setNewTraceList(new_trace);
				newView.setOldTraceList(old_trace);
				newView.setOldDataEdges(old_kept_data_edges);
				newView.setNewDataEdges(new_kept_data_edges);
				newView.setOldCtlEdges(old_kept_ctl_edges);
				newView.setNewCtlEdges(new_kept_ctl_edges);
				

				newView.otherViewsBehavior(observedFaultNode);//to mark the observed Fault initialy
				oldView.setCurrentNode(observedFault_old);
				oldView.otherViewsBehavior(observedFault_old);//to mark the observed Fault initialy
				newView.setCurrentNode(observedFaultNode);
				
			}

		});

	}
}
