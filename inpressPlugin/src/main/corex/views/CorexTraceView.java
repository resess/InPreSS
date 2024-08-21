package corex.views;

import java.util.HashMap;
import java.util.List;
import java.util.Stack;

import org.eclipse.jface.action.Action;
import org.eclipse.jface.action.IMenuListener;
import org.eclipse.jface.action.IMenuManager;
import org.eclipse.jface.action.IToolBarManager;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.IActionBars;

import corex.model.PairList;
import corex.separatesnapshots.DiffMatcher;
import microbat.Activator;
import microbat.model.trace.Trace;
import microbat.model.trace.TraceNode;
import microbat.model.value.VarValue;
import microbat.views.ImageUI;
import microbat.views.TraceView;
import sav.common.core.Pair;

public abstract class CorexTraceView extends TraceView {
	protected PairList pairList;
	protected DiffMatcher diffMatcher;
	protected List<TraceNode> new_kept_nodes;
	protected List<TraceNode> old_kept_nodes;
	protected HashMap<TraceNode, List<Pair<TraceNode, VarValue>>> new_kept_data_edges;
	protected HashMap<TraceNode, List<Pair<TraceNode, VarValue>>> old_kept_data_edges;
	protected HashMap<TraceNode, List<TraceNode>> new_kept_ctl_edges;
	protected HashMap<TraceNode, List<TraceNode>> old_kept_ctl_edges;
	protected List<TraceNode> new_trace_nodes;
	protected List<TraceNode> old_trace_nodes;
	protected Trace new_trace;
	protected Trace old_trace;
	
	@Override
	protected void appendMenuForTraceStep() {
		menuMgr.setRemoveAllWhenShown(true);
		menuMgr.addMenuListener(new IMenuListener() {
			@Override
			public void menuAboutToShow(IMenuManager manager) {
				Action forSearchAction = createForSearchAction();
				Action controlMendingAction = createControlMendingAction();
				menuMgr.add(forSearchAction);
				menuMgr.add(controlMendingAction);
			}
		});
		
		listViewer.getTree().setMenu(menuMgr.createContextMenu(listViewer.getTree()));
	}

	protected abstract Action createControlMendingAction();
	
	
	@Override
	public void createPartControl(Composite parent) {
		super.createPartControl(parent);
		hookActionsOnToolBar();
	}
	
	private Stack<TraceNode> visitedNodeStack = new Stack<>();

	private void hookActionsOnToolBar() {
		IActionBars actionBars = getViewSite().getActionBars();
		IToolBarManager toolBar = actionBars.getToolBarManager();
		
		Action undoAction = new Action("Undo"){
			public void run(){
				if(!visitedNodeStack.isEmpty()) {
					TraceNode node = visitedNodeStack.pop();
					jumpToNode(trace, node.getOrder(), true);
				}
			}
		};
		undoAction.setImageDescriptor(Activator.getDefault().getImageRegistry().getDescriptor(ImageUI.UNDO_MARK));
		
		
		toolBar.add(undoAction);
		
	}

	public Stack<TraceNode> getVisitedNodeStack() {
		return visitedNodeStack;
	}
	
	public void recordVisitedNode(TraceNode node) {
		this.visitedNodeStack.push(node);
	}
	
	public HashMap<TraceNode, List<Pair<TraceNode, VarValue>>> getKeptDataEdges() {
		return this.old_kept_data_edges;
	}
	public HashMap<TraceNode, List<TraceNode>> getKeptCtlEdges() {
		return this.old_kept_ctl_edges;
	}
	public List<TraceNode> getKeptNodes() {
		return this.old_kept_nodes;
	}
	
}
