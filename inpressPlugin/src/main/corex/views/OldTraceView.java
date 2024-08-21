package corex.views;

import java.io.File;
import java.util.HashMap;
import java.util.List;

import org.eclipse.jface.action.Action;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;

import corex.editors.CompareEditor;
import corex.editors.CompareTextEditorInput;
import corex.empiricalstudy.RootCauseFinder;
import corex.model.PairList;
import corex.model.TraceNodePair;
import corex.separatesnapshots.DiffMatcher;
import corex.separatesnapshots.diff.FilePairWithDiff;
import microbat.model.BreakPoint;
import microbat.model.ClassLocation;
import microbat.model.trace.Trace;
import microbat.model.trace.TraceNode;
import microbat.model.value.VarValue;
import microbat.util.MicroBatUtil;
import sav.common.core.Pair;

public class OldTraceView extends CorexTraceView {

	public static final String ID = "corex.evalView.oldTraceView";
	
	public OldTraceView() {
	}
	
	@Override
	protected Action createControlMendingAction() {
		Action action = new Action() {
			public void run() {
				if (listViewer.getSelection().isEmpty()) {
					return;
				}

				if (listViewer.getSelection() instanceof IStructuredSelection) {
					IStructuredSelection selection = (IStructuredSelection) listViewer.getSelection();
					TraceNode node = (TraceNode) selection.getFirstElement();
					System.out.println("this is it:" + node);
					NewTraceView newTraceView = CorexViews.getNewTraceView();
					ClassLocation correspondingLocation = diffMatcher.findCorrespondingLocation(node.getBreakPoint(), true);
					TraceNode otherControlDom = new RootCauseFinder().findControlMendingNodeOnOtherTrace(node, pairList, 
							newTraceView.getTrace(), true, correspondingLocation, diffMatcher);
					System.out.println("this is it:" + otherControlDom);
					if (otherControlDom != null) {
						newTraceView.otherViewsBehavior(otherControlDom);
						newTraceView.jumpToNode(newTraceView.getTrace(), otherControlDom.getOrder(), refreshProgramState);
					}
					
				}
				
			}
			
			public String getText() {
				return "control mend";
			}
		};
		
		return action;
	}
	
	private void openInCompare(CompareTextEditorInput input, TraceNode node) {
		IWorkbench wb = PlatformUI.getWorkbench();
		IWorkbenchWindow win = wb.getActiveWorkbenchWindow();
		IWorkbenchPage workBenchPage = win.getActivePage();

		IEditorPart editPart = workBenchPage.findEditor(input);
		if(editPart != null){
			workBenchPage.activate(editPart);
			CompareEditor editor = (CompareEditor)editPart;
			editor.highLight(node);
		}
		else{
			try {
				workBenchPage.openEditor(input, CompareEditor.ID);
			} catch (PartInitException e) {
				e.printStackTrace();
			}
		}
		
	}

	class CompareFileName {
		String buggyFileName;
		String fixFileName;

		public CompareFileName(String buggyFileName, String fixFileName) {
			super();
			this.buggyFileName = buggyFileName;
			this.fixFileName = fixFileName;
		}

	}

	private CompareFileName generateCompareFile(BreakPoint breakPoint, DiffMatcher matcher) {
		String fixPath = breakPoint.getFullJavaFilePath();
		String buggyPath = "null";

		FilePairWithDiff fileDiff = getDiffMatcher().findDiffByTargetFile(breakPoint);
		if (getDiffMatcher() == null || fileDiff == null) {
			String fixBase = diffMatcher.getFixPath();
			String content = fixPath.substring(fixBase.length(), fixPath.length());
			buggyPath = diffMatcher.getBuggyPath() + content;		
			if(!new File(buggyPath).exists()){
				buggyPath = fixPath;
			}
			
		} else {
			buggyPath = fileDiff.getSourceFile();
		}
		
		CompareFileName cfn = new CompareFileName(buggyPath, fixPath);
		return cfn;
	}

	@Override
	protected void markJavaEditor(TraceNode node) {
		BreakPoint breakPoint = node.getBreakPoint();
		
		CompareFileName cfn = generateCompareFile(breakPoint, getDiffMatcher());

		CompareTextEditorInput input = new CompareTextEditorInput(node, this.pairList, 
				cfn.buggyFileName, cfn.fixFileName, getDiffMatcher(),this.new_trace, this.old_trace, this.new_trace_nodes, this.old_trace_nodes,this.new_kept_nodes,this.old_kept_nodes);

		openInCompare(input, node);

	}

	@Override
	protected void otherViewsBehavior(TraceNode correctNode) {
		if (this.refreshProgramState) {
			
			StepPropertyView stepPropertyView = null;
			try {
				stepPropertyView = (StepPropertyView)PlatformUI.getWorkbench().
						getActiveWorkbenchWindow().getActivePage().showView(StepPropertyView.ID);
			} catch (PartInitException e) {
				e.printStackTrace();
			}
			
			TraceNodePair pair = pairList.findByAfterNode(correctNode);			
			correctNode.toString();
			TraceNode buggyNode = null;
			if(pair != null){
				buggyNode = pair.getBeforeNode();
				if (buggyNode != null) {
					NewTraceView buggyTraceView = CorexViews.getNewTraceView();
					buggyTraceView.jumpToNode(buggyTraceView.getTrace(), buggyNode.getOrder(), false);
				}
			}
//			System.out.println("Here in old Trace:"+new_kept_data_edges);
//			System.out.println("Here:"+old_kept_data_edges);
			if(this.kept_nodes.contains(correctNode))
				stepPropertyView.refresh(correctNode, buggyNode, diffMatcher, pairList, new_kept_data_edges, new_kept_ctl_edges, new_kept_nodes, old_kept_data_edges, old_kept_ctl_edges, old_kept_nodes);
		}

		markJavaEditor(correctNode);
	}

	public PairList getPairList() {
		return pairList;
	}

	public void setPairList(PairList pairList) {
		this.pairList = pairList;
	}

	public DiffMatcher getDiffMatcher() {
		return diffMatcher;
	}

	public void setDiffMatcher(DiffMatcher diffMatcher) {
		this.diffMatcher = diffMatcher;
	}
	
	public void setNewKeptList(List<TraceNode> trace) {
		this.new_kept_nodes = trace;
	}
	public void setOldKeptList(List<TraceNode> trace) {
		this.old_kept_nodes = trace;
	}

	public void setNewTraceList(List<TraceNode> trace) {
		this.new_trace_nodes = trace;		
	}

	public void setOldTraceList(List<TraceNode> trace) {
		this.old_trace_nodes = trace;
		
	}
	public void setNewDataEdges(HashMap<TraceNode, List<Pair<TraceNode, VarValue>>> edges) {
		this.new_kept_data_edges = edges;		
	}

	public void setOldDataEdges(HashMap<TraceNode, List<Pair<TraceNode, VarValue>>> edges) {
		this.old_kept_data_edges = edges;		
	}
	public void setNewCtlEdges(HashMap<TraceNode, List<TraceNode>> edges) {
		this.new_kept_ctl_edges = edges;		
	}

	public void setOldCtlEdges(HashMap<TraceNode, List<TraceNode>> edges) {
		this.old_kept_ctl_edges = edges;		
	}
	
	public void setNewTrace(Trace trace) {
		this.new_trace = trace;		
	}

	public void setOldTrace(Trace trace) {
		this.old_trace = trace;
		
	}
	@Override
	public HashMap<TraceNode, List<Pair<TraceNode, VarValue>>> getKeptDataEdges() {
		return this.old_kept_data_edges;
	}
	@Override
	public HashMap<TraceNode, List<TraceNode>> getKeptCtlEdges() {
		return this.old_kept_ctl_edges;
	}
	@Override
	public List<TraceNode> getKeptNodes() {
		return this.old_kept_nodes;
	}


	


}
