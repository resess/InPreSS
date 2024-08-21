package corex.views;

import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;

public class CorexViews {
	
	public static OldTraceView getOldTraceView(){
		OldTraceView view = null;
		try {
			view = (OldTraceView)PlatformUI.getWorkbench().
					getActiveWorkbenchWindow().getActivePage().showView(OldTraceView.ID);
		} catch (PartInitException e) {
			e.printStackTrace();
		}
		
		return view;
	}
	
	public static NewTraceView getNewTraceView(){
		NewTraceView view = null;
		try {
			view = (NewTraceView)PlatformUI.getWorkbench().
					getActiveWorkbenchWindow().getActivePage().showView(NewTraceView.ID);
		} catch (PartInitException e) {
			e.printStackTrace();
		}
		
		return view;
	}
	
	public static StepPropertyView getStepPropertyView(){
		StepPropertyView view = null;
		try {
			view = (StepPropertyView)PlatformUI.getWorkbench().
					getActiveWorkbenchWindow().getActivePage().showView(StepPropertyView.ID);
		} catch (PartInitException e) {
			e.printStackTrace();
		}
		
		return view;
	}
}
