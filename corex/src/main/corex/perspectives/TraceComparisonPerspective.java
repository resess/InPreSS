package corex.perspectives;

import org.eclipse.ui.IFolderLayout;
import org.eclipse.ui.IPageLayout;
import org.eclipse.ui.IPerspectiveFactory;
import org.eclipse.ui.console.IConsoleConstants;

import corex.views.NewTraceView;
import corex.views.OldTraceView;
import corex.views.StepPropertyView;

public class TraceComparisonPerspective implements IPerspectiveFactory {

	private IPageLayout factory;

	public TraceComparisonPerspective() {
		super();
	}

	public void createInitialLayout(IPageLayout factory) {
		this.factory = factory;
		addViews();
	}

	private void addViews() {
		// Creates the overall folder layout. 
		// Note that each new Folder uses a percentage of the remaining EditorArea.
		IFolderLayout topLeft =
				factory.createFolder(
						"topLeft",
						IPageLayout.LEFT,
						0.2f,
						factory.getEditorArea());
		topLeft.addView(OldTraceView.ID); 
//		topLeft.addView(IPageLayout.ID_PROJECT_EXPLORER);
		
		IFolderLayout topRight =
				factory.createFolder(
						"topRight",
						IPageLayout.RIGHT,
						0.8f,
						factory.getEditorArea());
		topRight.addView(NewTraceView.ID); 
		
		IFolderLayout bottom =
			factory.createFolder(
				"bottom", //NON-NLS-1
				IPageLayout.BOTTOM,
				0.5f,
				factory.getEditorArea());
//		bottom.addView(IPageLayout.ID_PROBLEM_VIEW);
		bottom.addView(StepPropertyView.ID);
		bottom.addPlaceholder(IConsoleConstants.ID_CONSOLE_VIEW);
	}

}
