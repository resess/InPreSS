package corex.views;

import java.util.HashMap;
import java.util.List;

import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.SashForm;
import org.eclipse.swt.custom.ScrolledComposite;
import org.eclipse.swt.graphics.Point;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.part.ViewPart;

import corex.StepChangeType;
import corex.StepChangeTypeChecker;
import corex.model.PairList;
import corex.separatesnapshots.DiffMatcher;
import microbat.model.trace.Trace;
import microbat.model.trace.TraceNode;
import microbat.model.value.VarValue;
import microbat.views.TraceView;
import sav.common.core.Pair;

public class StepPropertyView extends ViewPart {

	public static final String ID = "corex.view.stepProperty";
	
	private StepDetailUI buggyDetailUI;
	private StepDetailUI correctDetailUI;
	
	private HashMap<TraceNode, List<Pair<TraceNode, VarValue>>> old_kept_data_edges;
	private HashMap<TraceNode, List<TraceNode>> old_kept_ctl_edges;
	private List<TraceNode> old_kept_nodes;
	private HashMap<TraceNode, List<Pair<TraceNode, VarValue>>> new_kept_data_edges;
	private HashMap<TraceNode, List<TraceNode>> new_kept_ctl_edges;
	private List<TraceNode> new_kept_nodes;
	
	public StepPropertyView() {
	}

	@Override
	public void createPartControl(Composite parent) {
		GridLayout parentLayout = new GridLayout(1, true);
		parent.setLayout(parentLayout);
		
		SashForm sashForm = new SashForm(parent, SWT.HORIZONTAL);
		GridData data = new GridData(SWT.FILL, SWT.FILL, true, true);
		sashForm.setLayoutData(data);
		
		
		createScrolledComposite(sashForm, OldTraceView.ID, new_kept_data_edges, new_kept_ctl_edges, new_kept_nodes,  old_kept_data_edges,  old_kept_ctl_edges, old_kept_nodes);
		createScrolledComposite(sashForm, NewTraceView.ID, new_kept_data_edges, new_kept_ctl_edges, new_kept_nodes,  old_kept_data_edges,  old_kept_ctl_edges, old_kept_nodes);
		

		sashForm.setWeights(new int[]{50, 50});
	}
	
	private void createScrolledComposite(SashForm sashForm, String viewID, 
			HashMap<TraceNode, List<Pair<TraceNode, VarValue>>> new_kept_data_edges, HashMap<TraceNode, List<TraceNode>> new_kept_ctl_edges,
			List<TraceNode> new_kept_nodes, 
			HashMap<TraceNode, List<Pair<TraceNode, VarValue>>> old_kept_data_edges, HashMap<TraceNode, List<TraceNode>> old_kept_ctl_edges,
			List<TraceNode> old_kept_nodes){
		ScrolledComposite panel = new ScrolledComposite(sashForm, SWT.H_SCROLL | SWT.V_SCROLL);
		panel.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
		panel.setExpandHorizontal(true);
		panel.setExpandVertical(true);
		CorexTraceView view = null;
		
		if(viewID.equals(OldTraceView.ID)){
			try {
				view = (OldTraceView)PlatformUI.getWorkbench().
						getActiveWorkbenchWindow().getActivePage().showView(OldTraceView.ID);
			} catch (PartInitException e) {
				e.printStackTrace();
			}
		}
		else{
			try {
				view = (NewTraceView)PlatformUI.getWorkbench().
						getActiveWorkbenchWindow().getActivePage().showView(NewTraceView.ID);
			} catch (PartInitException e) {
				e.printStackTrace();
			}
		}
		
		Composite comp = createPanel(panel, view, new_kept_data_edges,new_kept_ctl_edges, new_kept_nodes,  old_kept_data_edges,  old_kept_ctl_edges, old_kept_nodes);
		panel.setContent(comp);
//		panel.setAlwaysShowScrollBars(true);
//		panel.setMinSize(comp.computeSize(SWT.DEFAULT, SWT.DEFAULT));
		Point point = comp.computeSize(SWT.DEFAULT, SWT.DEFAULT);
		panel.setMinHeight(point.y);
	}

	private Composite createPanel(Composite panel, CorexTraceView view, 
			HashMap<TraceNode, List<Pair<TraceNode, VarValue>>> new_kept_data_edges, HashMap<TraceNode, List<TraceNode>> new_kept_ctl_edges, List<TraceNode> new_kept_nodes, 
			HashMap<TraceNode, List<Pair<TraceNode, VarValue>>> old_kept_data_edges, HashMap<TraceNode, List<TraceNode>> old_kept_ctl_edges, List<TraceNode> old_kept_nodes) {
		GridLayout layout = new GridLayout();
		layout.numColumns = 1;
		panel.setLayout(layout);
		
		if(view instanceof NewTraceView){
			buggyDetailUI = new StepDetailUI(view, null, true, new_kept_data_edges, new_kept_ctl_edges, new_kept_nodes);			
			return buggyDetailUI.createDetails(panel);
		}
		else if(view instanceof OldTraceView){
			correctDetailUI = new StepDetailUI(view, null, false, old_kept_data_edges, old_kept_ctl_edges, old_kept_nodes);
			return correctDetailUI.createDetails(panel);
		}
		
		return null;
	}
	

	
	public void refresh(TraceNode correctNode, TraceNode buggyNode, DiffMatcher diffMatcher, PairList pairList, 
			HashMap<TraceNode, List<Pair<TraceNode, VarValue>>> new_kept_data_edges, HashMap<TraceNode, List<TraceNode>> new_kept_ctl_edges,
			List<TraceNode> new_kept_nodes, HashMap<TraceNode, List<Pair<TraceNode, VarValue>>> old_kept_data_edges,  HashMap<TraceNode, List<TraceNode>> old_kept_ctl_edges,List<TraceNode> old_kept_nodes){
		Trace buggyTrace = CorexViews.getNewTraceView().getTrace();
		Trace correctTrace = CorexViews.getOldTraceView().getTrace();
		StepChangeTypeChecker checker = new StepChangeTypeChecker(buggyTrace, correctTrace);
		

		if(buggyDetailUI != null && buggyNode != null){
			StepChangeType changeType = checker.getTypeForPrinting(buggyNode, true, pairList, diffMatcher);
			buggyDetailUI.refresh(buggyNode, changeType, new_kept_data_edges, new_kept_ctl_edges, new_kept_nodes);
		}
		if(buggyNode==null) {
			buggyDetailUI.refresh(buggyNode, null, new_kept_data_edges, new_kept_ctl_edges, new_kept_nodes);
		}
		
		if(correctDetailUI != null && correctNode != null){
			StepChangeType changeType = checker.getTypeForPrinting(correctNode, false, pairList, diffMatcher);
			correctDetailUI.refresh(correctNode, changeType,  old_kept_data_edges, old_kept_ctl_edges, old_kept_nodes);
		}
		if(correctNode==null) {
			correctDetailUI.refresh(correctNode, null, old_kept_data_edges, old_kept_ctl_edges, old_kept_nodes);
		}
	}
	
	@Override
	public void setFocus() {

	}

}
