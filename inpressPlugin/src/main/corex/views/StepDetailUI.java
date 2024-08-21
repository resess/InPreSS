package corex.views;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.List;

import org.eclipse.jface.action.Action;
import org.eclipse.jface.action.GroupMarker;
import org.eclipse.jface.action.IMenuListener;
import org.eclipse.jface.action.IMenuManager;
import org.eclipse.jface.action.MenuManager;
import org.eclipse.jface.viewers.CheckStateChangedEvent;
import org.eclipse.jface.viewers.CheckboxTreeViewer;
import org.eclipse.jface.viewers.ICheckStateListener;
import org.eclipse.jface.viewers.ICheckStateProvider;
import org.eclipse.jface.viewers.ILabelProviderListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.ITableLabelProvider;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.ITreeViewerListener;
import org.eclipse.jface.viewers.TreeExpansionEvent;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.SashForm;
import org.eclipse.swt.events.KeyAdapter;
import org.eclipse.swt.events.KeyEvent;
import org.eclipse.swt.events.MouseEvent;
import org.eclipse.swt.events.MouseListener;
import org.eclipse.swt.graphics.Font;
import org.eclipse.swt.graphics.FontData;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Menu;
import org.eclipse.swt.widgets.MessageBox;
import org.eclipse.swt.widgets.Text;
import org.eclipse.swt.widgets.Tree;
import org.eclipse.swt.widgets.TreeColumn;
import org.eclipse.swt.widgets.TreeItem;
import org.eclipse.ui.IWorkbenchActionConstants;
import org.eclipse.ui.PlatformUI;

import corex.StepChangeType;
import microbat.algorithm.graphdiff.GraphDiff;
import microbat.model.BreakPointValue;
import microbat.model.UserInterestedVariables;
import microbat.model.trace.Trace;
import microbat.model.trace.TraceNode;
import microbat.model.value.ReferenceValue;
import microbat.model.value.VarValue;
import microbat.model.value.VirtualValue;
import microbat.model.variable.Variable;
import microbat.recommendation.ChosenVariableOption;
import microbat.recommendation.ChosenVariableOption2;
import microbat.recommendation.UserFeedback;
import microbat.util.JavaUtil;
import microbat.util.Settings;
import microbat.util.TempVariableInfo;
import microbat.views.ImageUI;
import sav.common.core.Pair;
import sav.strategies.dto.AppJavaClassPath;

public class StepDetailUI {
	
	public static final String RW = "rw";
	public static final String STATE = "state";
	private TraceNode currentNode;
	private HashMap<TraceNode, List<Pair<TraceNode, VarValue>>> kept_data_edges;
	private HashMap<TraceNode, List<TraceNode>> kept_ctl_edges;
	private List<TraceNode> kept_nodes;
	
	public UserInterestedVariables interestedVariables = new UserInterestedVariables();
	List<Pair<TraceNode, VarValue>> interesetedSelected = new ArrayList<>();
	
	private UserFeedback feedback = new UserFeedback();


	class FeedbackSubmitListener implements MouseListener{
		public void mouseUp(MouseEvent e) {}
		public void mouseDoubleClick(MouseEvent e) {}
		
		private void openChooseFeedbackDialog(){
			MessageBox box = new MessageBox(PlatformUI.getWorkbench()
					.getDisplay().getActiveShell());
			box.setMessage("Please tell me whether this step is correct or not!");
			box.open();
		}
		
		public void mouseDown(MouseEvent e) {
						
			if (feedback == null) {
				openChooseFeedbackDialog();
			} 
			else {
				Trace trace = traceView.getTrace();
				
				TraceNode suspiciousNode = null;
				if(dataButton.getSelection()){
					Object[] objList = readVariableTreeViewer.getCheckedElements();
					if(objList.length!=0) {
						Object obj = objList[0];
						if(obj instanceof Pair<?,?>) {
//							VarValue readVar = (VarValue)obj;	
							Pair pair= (Pair<TraceNode,VarValue>)(obj);			
							TraceNode target = (TraceNode)pair.first();
							//to go over only the kept nodes
							if(traceView.getKeptDataEdges().keySet().contains(currentNode)) 
								if(traceView.getKeptDataEdges().get(currentNode)!=null)
									if(traceView.getKeptNodes().contains(target))  		
										suspiciousNode = target;
//									for(Pair<TraceNode, VarValue> dep: traceView.getKeptDataEdges().get(currentNode)) {										
//										if(traceView.getKeptNode().contains(dep.first())&&dep.second().getVarName().equals(readVar.getVarName())) { 		
//											suspiciousNode = dep.first();
//											break;
//										}
//									}
							
//							suspiciousNode = trace.findDataDependency(currentNode, readVar);
						}
					}
				}
				else if(controlButton.getSelection()){
					
					//to go over only the kept nodes
					if(traceView.getKeptCtlEdges().keySet().contains(currentNode)) 
						if(traceView.getKeptCtlEdges().get(currentNode)!=null)
							for(TraceNode dep: traceView.getKeptCtlEdges().get(currentNode)) {										
								if(traceView.getKeptNodes().contains(dep)) {		
									suspiciousNode = dep;
									break;
								}
							}	
					
//					suspiciousNode = currentNode.getInvocationMethodOrDominator();
				}
				
				if(suspiciousNode != null){
					traceView.recordVisitedNode(currentNode);
					jumpToNode(trace, suspiciousNode);	
				}
			}
		}
		
		private void jumpToNode(Trace trace, TraceNode suspiciousNode) {
			traceView.jumpToNode(trace, suspiciousNode.getOrder(), true);
		}
	}
	
	@SuppressWarnings("unchecked")
	class RWVariableContentProvider implements ITreeContentProvider {
		/**
		 * rw is true means read, and rw is false means write.
		 */
		boolean rw;

		public RWVariableContentProvider(boolean rw) {
			this.rw = rw;
		}

		@Override
		public void dispose() {

		}

		@Override
		public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {

		}

		@Override
		public Object[] getElements(Object inputElement) {
			if (inputElement instanceof ArrayList) {
				ArrayList<Pair<TraceNode,VarValue>> elements = (ArrayList<Pair<TraceNode,VarValue>>) inputElement;
				return elements.toArray(new Pair<?,?>[0]);
			}

			return null;
		}

		@Override
		public Object[] getChildren(Object parentElement) {
			Pair<TraceNode, VarValue> pair = (Pair<TraceNode, VarValue>)parentElement;
			if (pair.second() instanceof ReferenceValue) {
				ReferenceValue refValue = (ReferenceValue)pair.second();				
//			if (parentElement instanceof ReferenceValue) {
//				ReferenceValue refValue = (ReferenceValue)parentElement;
					
				if(refValue.getChildren()==null){
					return null;
				}
				
				return refValue.getChildren().toArray(new VarValue[0]);
			}

			return null;
		}

		@Override
		public Object getParent(Object element) {
			return null;
		}

		@Override
		public boolean hasChildren(Object element) {
			Object[] children = getChildren(element);
			if (children == null || children.length == 0) {
				return false;
			} else {
				return true;
			}
		}

	}

	class RWVarListener implements ICheckStateListener {
		private String RWType;

		public RWVarListener(String RWType) {
			this.RWType = RWType;
		}

		@Override
		public void checkStateChanged(CheckStateChangedEvent event) {
			Object obj = event.getElement();
			
			VarValue value = null;

			if (obj instanceof Pair<?,?>) {
				Pair<TraceNode,VarValue> pair = (Pair<TraceNode,VarValue>)obj;
				if(!interesetedSelected.contains(pair)) {
					interesetedSelected.add(pair);				
//				value = (VarValue) obj;
//				value = pair.second();
//				Trace trace = traceView.getTrace();
//
//				String varID = value.getVarID();

//				if (!interestedVariables.contains(value)) {
//					interestedVariables.add(trace.getCheckTime(), value);
//
//					ChosenVariableOption option = feedback.getOption();
//					if (option == null) {
//						option = new ChosenVariableOption(null,null);
//					}
//
//					if (this.RWType.equals(Variable.READ)) {
//						option.setReadVar(value);					
//					}
////					if (this.RWType.equals(Variable.WRITTEN)) {
////						option.setWrittenVar(value);
////					}
//					feedback.setOption(option);
//
//					TempVariableInfo.variableOption = option;
//					TempVariableInfo.line = currentNode.getLineNumber();
//					String cuName = currentNode.getBreakPoint().getDeclaringCompilationUnitName();
//					TempVariableInfo.cu = JavaUtil.findCompilationUnitInProject(cuName, traceView.getTrace().getAppJavaClassPath());
				} else {
//					interestedVariables.remove(value);
					interesetedSelected.remove(pair);
				}

//				setChecks(writtenVariableTreeViewer, RW);
				setChecks(readVariableTreeViewer, RW);
				//setChecks(stateTreeViewer, STATE);

//				writtenVariableTreeViewer.refresh();
				readVariableTreeViewer.refresh();
				//stateTreeViewer.refresh();

			}

		}
	}

	class VariableCheckStateProvider implements ICheckStateProvider {

		@Override
		public boolean isChecked(Object element) {			
			VarValue value = null;
			if (element instanceof Pair<?,?>) {
				Pair<TraceNode,VarValue> pair = (Pair<TraceNode,VarValue>)element;
				value = pair.second();
			} else if (element instanceof GraphDiff) {
				value = (VarValue) ((GraphDiff) element).getChangedNode();
			}

			if (currentNode != null) {
				if (interestedVariables.contains(value)) {
					return true;
				}
			}
			return false;
		}
		
//		@Override
//		public boolean isChecked(Object element) {
//
//			VarValue value = null;
//			if (element instanceof VarValue) {
//				value = (VarValue) element;
//			} else if (element instanceof GraphDiff) {
//				value = (VarValue) ((GraphDiff) element).getChangedNode();
//			}
//
//			if (currentNode != null) {
//				if (interestedVariables.contains(value)) {
//					return true;
//				}
//			}
//			return false;
//		}

		@Override
		public boolean isGrayed(Object element) {
			return false;
		}

	}

	class VariableContentProvider implements ITreeContentProvider {
		public void dispose() {
		}

		public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {
		}

//		public Object[] getElements(Object inputElement) {
//			if (inputElement instanceof BreakPointValue) {
//				BreakPointValue value = (BreakPointValue) inputElement;
//				return value.getChildren().toArray(new VarValue[0]);
//			} else if (inputElement instanceof ReferenceValue) {
//				ReferenceValue value = (ReferenceValue) inputElement;
//				VarValue[] list = value.getChildren().toArray(new VarValue[0]);
//				if (list.length != 0) {
//					return list;
//				} else {
//					return null;
//				}
//			}
//
//			return null;
//		}
		public Object[] getElements(Object inputElement) {
			if(inputElement instanceof Pair<?,?>) {
				Pair<TraceNode,VarValue> pair = (Pair<TraceNode,VarValue>)inputElement;
				VarValue value = pair.second(); 
				if (value instanceof BreakPointValue) {
					BreakPointValue var_value = (BreakPointValue) value;
					return var_value.getChildren().toArray(new VarValue[0]);
				} else if (value instanceof ReferenceValue) {
					ReferenceValue var_value = (ReferenceValue) value;
					VarValue[] list = var_value.getChildren().toArray(new VarValue[0]);
					if (list.length != 0) {
						return list;
					} else {
						return null;
					}
				}
			}

			return null;
		}

		public Object[] getChildren(Object parentElement) {
			return getElements(parentElement);
		}

		public Object getParent(Object element) {
			return null;
		}

//		public boolean hasChildren(Object element) {
//			if (element instanceof ReferenceValue) {
//				ReferenceValue rValue = (ReferenceValue) element;
//				List<VarValue> children = rValue.getChildren();
//				return children != null && !children.isEmpty();
//			}
//			return false;
//		}
		public boolean hasChildren(Object element) {
			if(element instanceof Pair<?,?>) {
				Pair<TraceNode,VarValue> pair = (Pair<TraceNode,VarValue>)element;
				VarValue value = pair.second();
				if (value instanceof ReferenceValue) {
					ReferenceValue rValue = (ReferenceValue) value;
					List<VarValue> children = rValue.getChildren();
					return children != null && !children.isEmpty();
				}
			}
			return false;
		}

	}
	class VariableLabelProviderWritten implements ITableLabelProvider {
		private StepChangeType changeType;
		private boolean isOnBefore;
		private TraceNode currentNode;
		
		public VariableLabelProviderWritten(TraceNode node, StepChangeType changeType, boolean isOnBefore) {
			this.changeType = changeType;
			this.isOnBefore = isOnBefore;
			this.currentNode = node;
		}

		public void addListener(ILabelProviderListener listener) {
		}

		public void dispose() {
		}

		public boolean isLabelProperty(Object element, String property) {
			return false;
		}

		public void removeListener(ILabelProviderListener listener) {
		}

//		public Image getColumnImage(Object element, int columnIndex) {
//			if (element instanceof VarValue && columnIndex==0) {
//				VarValue varValue = (VarValue) element;
//				if(changeType.getType()==StepChangeType.DAT) {
//					for(Pair<VarValue, VarValue> pair: changeType.getWrongVariableList()) {
//						VarValue var = (this.isOnBefore) ? pair.first() : pair.second();
//						if(var.getVarID().equals(varValue.getVarID())) {
//							return Settings.imageUI.getImage(ImageUI.QUESTION_MARK);
//						}
//					}
//				}
//			}
//			
//			return null;
//		}
		
		public Image getColumnImage(Object element, int columnIndex) {
			if (element instanceof Pair<?,?> && columnIndex==0) {
				Pair edge= (Pair<TraceNode,VarValue>)(element);			
				VarValue varValue = (VarValue) edge.second();
				if(changeType.getType()==StepChangeType.DAT) {
					for(Pair<VarValue, VarValue> pair: changeType.getWrongVariableList()) {
						VarValue var = (this.isOnBefore) ? pair.first() : pair.second();
						if(var.getVarID().equals(varValue.getVarID())) {
							return Settings.imageUI.getImage(ImageUI.QUESTION_MARK);
						}
					}
				}
			}
			
			return null;
		}

		public String getColumnText(Object element, int columnIndex) {
//			if (element instanceof VarValue) {
//				VarValue varValue = (VarValue) element;
			if (element instanceof Pair<?,?>) {
				Pair edge= (Pair<TraceNode,VarValue>)(element);			
				VarValue varValue = (VarValue) edge.second();
				TraceNode target = (TraceNode) edge.first();
				switch (columnIndex) {
				case 0:
					String type = varValue.getType();
					if (type.contains(".")) {
						type = type.substring(type.lastIndexOf(".") + 1, type.length());
					}
					return type;
				case 1:
					String name = varValue.getVarName();
					if (varValue instanceof VirtualValue) {
						String methodName = name.substring(name.indexOf(":") + 1);
						name = "return from " + methodName + "()";
					}	
					return name;
				case 2:
					String value = varValue.getStringValue();
					
					return value;
//				case 3:
//					String id = varValue.getVarID();
//					String aliasVarID = varValue.getAliasVarID();
//					if(aliasVarID != null){
//						return id + (" aliasID:" + aliasVarID);
//					}
//					return id;					
				case 3:
					System.out.println(varValue);
					System.out.println(currentNode);
					System.out.println(varValue.getLableByTarget(currentNode));
					System.out.println(varValue.getSourcebyEdgeAndTarge(currentNode,varValue.getLableByTarget(currentNode)));
					String goingTo = varValue.getSourcebyEdgeAndTarge(currentNode,varValue.getLableByTarget(currentNode)).toString();
					return goingTo;
					
				case 4:
					String edge_label = varValue.getLableByTarget(currentNode);				
					return edge_label;
				}
			}

			return null;
		}

	}
	class VariableLabelProviderRead implements ITableLabelProvider {
		private StepChangeType changeType;
		private boolean isOnBefore;
		private TraceNode currentNode;
		
		public VariableLabelProviderRead(TraceNode node, StepChangeType changeType, boolean isOnBefore) {
			this.changeType = changeType;
			this.isOnBefore = isOnBefore;
			this.currentNode = node;
		}

		public void addListener(ILabelProviderListener listener) {
		}

		public void dispose() {
		}

		public boolean isLabelProperty(Object element, String property) {
			return false;
		}

		public void removeListener(ILabelProviderListener listener) {
		}

		public Image getColumnImage(Object element, int columnIndex) {
			if (element instanceof Pair<?,?> && columnIndex==0) {
				Pair edge= (Pair<TraceNode,VarValue>)(element);			
				VarValue varValue = (VarValue) edge.second();
				TraceNode target = (TraceNode) edge.first();
				
//				List<VarValue> values = new ArrayList<>();
//				if(varValue.getLableByTarget(target).contains("Compound")) {
//					   String function_vars = varValue.getLableByTarget(target).split("Func")[1];
//					   function_vars = function_vars.substring(function_vars.indexOf("(") + 1);
//					   function_vars = function_vars.substring(0, function_vars.lastIndexOf(")"));
//					   for(VarValue val: target.getWrittenVariables()) {
//						   if(function_vars.contains(val.getVarName()))
//							   values.add(val);							   
//					   }
//				}
					   
				
				if(changeType.getType()==StepChangeType.DAT) {
					for(Pair<VarValue, VarValue> pair: changeType.getWrongVariableList()) {
						VarValue var = (this.isOnBefore) ? pair.first() : pair.second();
						if(var.getVarID().equals(varValue.getVarID())) {
//							if(values.contains(var)) {
								return Settings.imageUI.getImage(ImageUI.EXCLAMATION_MARK);
						}
					}
				}
			}
			
			return null;
		}

		public String getColumnText(Object element, int columnIndex) {
			if (element instanceof Pair<?,?>) {
				Pair edge= (Pair<TraceNode,VarValue>)(element);			
				VarValue varValue = (VarValue) edge.second();
				TraceNode target = (TraceNode) edge.first();
//				System.out.println(varValue.getVarName());
//				System.out.println(target.toString());
//				System.out.println(varValue.getLableBySource(currentNode));
//				System.out.println(varValue.getLableByTarget(target));
//				VarValue varValue = (VarValue) element;
				switch (columnIndex) {
				case 0:
					String type = varValue.getType();
					if (type.contains(".")) {
						type = type.substring(type.lastIndexOf(".") + 1, type.length());
					}
					return type;
				case 1:
					String name = varValue.getVarName();
					if (varValue instanceof VirtualValue) {
						String methodName = name.substring(name.indexOf(":") + 1);
						name = "return from " + methodName + "()";
					}
					if(varValue.getLableByTarget(target).contains("Compound")) {
					   String function_vars = varValue.getLableByTarget(target).split("Func")[1];
					   function_vars = function_vars.substring(function_vars.indexOf("(") + 1);
					   function_vars = function_vars.substring(0, function_vars.lastIndexOf(")"));
					   name = name + "[" + function_vars + "]";				   
					   // f (c)
					}
					return name;
				case 2:
					String value = varValue.getStringValue();
					List<String> values = new ArrayList<>();
					if(varValue.getLableByTarget(target).contains("Compound")) {
						   String function_vars = varValue.getLableByTarget(target).split("Func")[1];
						   function_vars = function_vars.substring(function_vars.indexOf("(") + 1);
						   function_vars = function_vars.substring(0, function_vars.lastIndexOf(")"));
						   for(VarValue val: target.getWrittenVariables()) {
							   if(function_vars.contains(val.getVarName()))
								   values.add(val.getStringValue());							   
						   }
						   if(values.size()>0) {
							   value = value + "[";
							   for(int j=0; j<values.size();j++) {
									if(j!=values.size()-1)
										value = value + values.get(j) + ", ";
									else
										value = value + values.get(j);
								}
							   value = value +"]";
						   }
						  
						}
					return value;
//				case 3:
//					String id = varValue.getVarID();
//					String aliasVarID = varValue.getAliasVarID();
//					if(aliasVarID != null){
//						return id + (" aliasID:" + aliasVarID);
//					}
//					return id;					
				case 3:
					String comingFrom = target.toString();
					return comingFrom;
					
				case 4:
					String edge_lable = varValue.getLableByTarget(target);				
					return edge_lable;
				}
			}

			return null;
		}

	}

	//private CheckboxTreeViewer stateTreeViewer;
//	private CheckboxTreeViewer writtenVariableTreeViewer;
	private CheckboxTreeViewer readVariableTreeViewer;

	private ITreeViewerListener treeListener;
	private CorexTraceView traceView;
	private boolean isOnBefore;
	
	public StepDetailUI(CorexTraceView view, TraceNode node, boolean isOnBefore, HashMap<TraceNode, List<Pair<TraceNode, VarValue>>> data_edges, HashMap<TraceNode, List<TraceNode>> ctl_edges, List<TraceNode> nodes){
		this.traceView = view;
		this.currentNode = node;
		this.isOnBefore = isOnBefore;
		this.kept_data_edges = data_edges;
		this.kept_ctl_edges = ctl_edges;
		this.kept_nodes = nodes;
	}

	private void addListener() {

		treeListener = new ITreeViewerListener() {

			@Override
			public void treeExpanded(TreeExpansionEvent event) {

				setChecks(readVariableTreeViewer, RW);
//				setChecks(writtenVariableTreeViewer, RW);
				//setChecks(stateTreeViewer, STATE);

				Display.getDefault().asyncExec(new Runnable() {

					@Override
					public void run() {
						readVariableTreeViewer.refresh();
//						writtenVariableTreeViewer.refresh();
						//stateTreeViewer.refresh();
					}
				});

			}

			@Override
			public void treeCollapsed(TreeExpansionEvent event) {

			}
		};

		this.readVariableTreeViewer.addTreeListener(treeListener);
//		this.writtenVariableTreeViewer.addTreeListener(treeListener);
		//this.stateTreeViewer.addTreeListener(treeListener);

//		this.writtenVariableTreeViewer.addCheckStateListener(new RWVarListener(Variable.WRITTEN));
		this.readVariableTreeViewer.addCheckStateListener(new RWVarListener(Variable.READ));
		//this.stateTreeViewer.addCheckStateListener(new RWVarListener(Variable.READ));

	}
	
	private CheckboxTreeViewer createVarGroup(Composite variableForm, String groupName) {
		Group varGroup = new Group(variableForm, SWT.NONE);
		GridData data = new GridData(SWT.FILL, SWT.FILL, true, true);
		data.minimumHeight = 100;
		varGroup.setLayoutData(data);
		
		varGroup.setText(groupName);
		varGroup.setLayout(new FillLayout());
    
		Tree tree = new Tree(varGroup, SWT.H_SCROLL | SWT.V_SCROLL | SWT.FULL_SELECTION | SWT.CHECK);		
		tree.setHeaderVisible(true);
		tree.setLinesVisible(true);

		TreeColumn typeColumn = new TreeColumn(tree, SWT.LEFT);
		typeColumn.setAlignment(SWT.LEFT);
		typeColumn.setText("Variable Type");
		typeColumn.setWidth(100);
		
		TreeColumn nameColumn = new TreeColumn(tree, SWT.LEFT);
		nameColumn.setAlignment(SWT.LEFT);
		nameColumn.setText("Variable Name");
		nameColumn.setWidth(100);
		
		TreeColumn valueColumn = new TreeColumn(tree, SWT.LEFT);
		valueColumn.setAlignment(SWT.LEFT);
		valueColumn.setText("Variable Value");
		valueColumn.setWidth(100);
		
		if (groupName.equals("Read Variables: ")) {
			TreeColumn comingFromColumn = new TreeColumn(tree, SWT.LEFT);
			comingFromColumn.setAlignment(SWT.LEFT);
			comingFromColumn.setText("Coming From");
			comingFromColumn.setWidth(200);
			
			TreeColumn Edge = new TreeColumn(tree, SWT.LEFT);
			Edge.setAlignment(SWT.LEFT);
			Edge.setText("Edge Value");
			Edge.setWidth(200);
		}
//		else {			
//				TreeColumn comingFromColumn = new TreeColumn(tree, SWT.LEFT);
//				comingFromColumn.setAlignment(SWT.LEFT);
//				comingFromColumn.setText("Goring To");
//				comingFromColumn.setWidth(150);
//				
//				TreeColumn Edge = new TreeColumn(tree, SWT.LEFT);
//				Edge.setAlignment(SWT.LEFT);
//				Edge.setText("Edge Value");
//				Edge.setWidth(150);		
//		}
		
//		TreeColumn idColumn = new TreeColumn(tree, SWT.LEFT);
//		idColumn.setAlignment(SWT.LEFT);
//		idColumn.setText("ID");
//		idColumn.setWidth(200);

		CheckboxTreeViewer viewer = new CheckboxTreeViewer(tree);
		createContextMenu(viewer);
		return viewer;
	}
	
	/**
	 * Creates the context menu
	 *
	 * @param viewer
	 */
	protected void createContextMenu(final Viewer viewer) {
	    MenuManager contextMenu = new MenuManager("#ViewerMenu"); //$NON-NLS-1$
	    contextMenu.setRemoveAllWhenShown(true);
	    contextMenu.addMenuListener(new IMenuListener() {
	        @Override
	        public void menuAboutToShow(IMenuManager mgr) {
	            fillContextMenu(mgr, viewer);
	        }
	    });

	    Menu menu = contextMenu.createContextMenu(viewer.getControl());
	    viewer.getControl().setMenu(menu);
	}

	/**
	 * Fill dynamic context menu
	 *
	 * @param contextMenu
	 */
	protected void fillContextMenu(IMenuManager contextMenu, final Viewer viewer) {
	    contextMenu.add(new GroupMarker(IWorkbenchActionConstants.MB_ADDITIONS));

//	    contextMenu.add(new Action("Search next step reading this variable") {
//	        @Override
//	        public void run() {
//	        	IStructuredSelection selection = (IStructuredSelection) viewer.getSelection();
//	        	Object obj = selection.getFirstElement();
//	        	if(obj instanceof VarValue){
//	        		VarValue value = (VarValue)obj;
//	        		Trace trace = traceView.getTrace();
//	        		List<TraceNode> nodes = trace.findNextReadingTraceNodes(value, currentNode.getOrder());
//	        		if(!nodes.isEmpty()){
//	        			TraceNode n = nodes.get(0);
//	        			traceView.jumpToNode(trace, n.getOrder(), true);
//	        		}
////	        		traceView.jumpToNode(expression, true);
//	        	}
//	        }
//	    });
	    
	    contextMenu.add(new Action("Search next step reading this variable") {
	        @Override
	        public void run() {
	        	IStructuredSelection selection = (IStructuredSelection) viewer.getSelection();
//	        	Object obj = selection.getFirstElement();
	        	Object obj =  selection.getFirstElement();
//	        	if(obj instanceof VarValue){
	        	if(obj instanceof Pair<?,?>){
//	        		VarValue value = (VarValue)obj;
	        		VarValue value = ((Pair<TraceNode, VarValue>)obj).second();
	        		Trace trace = traceView.getTrace();
//	        		List<TraceNode> nodes = trace.findNextReadingTraceNodes(value, currentNode.getOrder());
	        		List<TraceNode> nodes = value.getNodesWhereVarIsUsed();
	        		if(!nodes.isEmpty()){
	        			TraceNode n = nodes.get(0);
	        			traceView.jumpToNode(trace, n.getOrder(), true);
	        		}
//	        		traceView.jumpToNode(expression, true);
	        	}
	        }
	    });
	    
	    //TODO: this does not make sense
	    contextMenu.add(new Action("Search previous step reading this variable") {
	        @Override
	        public void run() {
	        	IStructuredSelection selection = (IStructuredSelection) viewer.getSelection();
	        	Object obj = selection.getFirstElement();
	        	if(obj instanceof VarValue){
	        		VarValue value = (VarValue)obj;
	        		Trace trace = traceView.getTrace();
	        		List<TraceNode> nodes = trace.findPrevReadingTraceNodes(value, currentNode.getOrder());
	        		if(!nodes.isEmpty()){
	        			TraceNode n = nodes.get(0);
	        			traceView.jumpToNode(trace, n.getOrder(), true);
	        		}
	        	}
	        }
	    });
	    
	}

	public Composite createDetails(Composite panel) {
		Composite comp = new Composite(panel, SWT.NONE);
		
		comp.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
		comp.setLayout(new GridLayout(1, true));
		
		createSlicingGroup(comp);
		
		SashForm sashForm = new SashForm(comp, SWT.VERTICAL);
		GridData data = new GridData(SWT.FILL, SWT.FILL, true, true);
		sashForm.setLayoutData(data);
		
		this.readVariableTreeViewer = createVarGroup(sashForm, "Read Variables: ");
//		this.writtenVariableTreeViewer = createVarGroup(sashForm, "Written Variables: ");
		//this.stateTreeViewer = createVarGroup(comp, "States: ");
		
		
//		searchText = new Text(sashForm, SWT.BORDER);
//		FontData searchTextFont = searchText.getFont().getFontData()[0];
//		searchTextFont.setHeight(100);
//		searchText.setFont(new Font(Display.getCurrent(), searchTextFont));
//		data = new GridData(SWT.FILL, SWT.FILL, true, false);
//		searchText.setLayoutData(data);
//		data.minimumHeight = 100;
		
		
//		sashForm.setWeights(new int[]{50, 50});
		sashForm.setWeights(new int[]{100});
		
		
		
		addListener();
		
		return comp;
	}
	
	protected void addGPTTextListener(final Text searchText) {
		searchText.setText("Test");

	}
	
	private Button dataButton;
	private Button controlButton;
	
	
	
	private void createSlicingGroup(Composite panel) {
		Group slicingGroup = new Group(panel, SWT.NONE);
		GridData data = new GridData(SWT.FILL, SWT.TOP, true, false);
		data.minimumHeight = 35;
		slicingGroup.setLayoutData(data);
		
		GridLayout gl = new GridLayout(3, true);
		slicingGroup.setLayout(gl);
		
		dataButton = new Button(slicingGroup, SWT.RADIO);
		dataButton.setLayoutData(new GridData(SWT.LEFT, SWT.TOP, true, false));
		dataButton.setText("data ");
		
		
		controlButton = new Button(slicingGroup, SWT.RADIO);
		controlButton.setLayoutData(new GridData(SWT.LEFT, SWT.TOP, true, false));
		controlButton.setText("control ");
		
		Button submitButton = new Button(slicingGroup, SWT.PUSH);
		submitButton.setText("Go");
		GridData buttonData = new GridData(SWT.RIGHT, SWT.TOP, true, false);
		submitButton.setLayoutData(buttonData);
		buttonData.widthHint = 100;
//		Image image = new Image(PlatformUI.getWorkbench().getDisplay(),System.getProperty("user.dir")+"/icons/go.jpg");
//		submitButton.setImage(image);
		FeedbackSubmitListener fListener = new FeedbackSubmitListener();
		submitButton.addMouseListener(fListener);
	}
	
//	private void createWrittenVariableContent(TraceNode node,List<Pair<TraceNode,VarValue>> writtenVariables, StepChangeType changeType) {
//		this.writtenVariableTreeViewer.setContentProvider(new RWVariableContentProvider(false));
//		this.writtenVariableTreeViewer.setLabelProvider(new VariableLabelProviderWritten(node,changeType, isOnBefore));
//		this.writtenVariableTreeViewer.setInput(writtenVariables);	
//		
//		setChecks(this.writtenVariableTreeViewer, RW);
//
//		this.writtenVariableTreeViewer.refresh(true);
//		
//	}

	private void createReadVariableContect(TraceNode node, List<Pair<TraceNode,VarValue>> readVariables, StepChangeType changeType) {
		this.readVariableTreeViewer.setContentProvider(new RWVariableContentProvider(true));
		if(changeType!=null ) {
			this.readVariableTreeViewer.setLabelProvider(new VariableLabelProviderRead(node, changeType, isOnBefore));
			sortVarValues(readVariables);
		}
		this.readVariableTreeViewer.setInput(readVariables);	
		
		setChecks(this.readVariableTreeViewer, RW);

		this.readVariableTreeViewer.refresh(true);
	}

//	private void createStateContent(BreakPointValue value){
//		this.stateTreeViewer.setContentProvider(new VariableContentProvider());
//		this.stateTreeViewer.setLabelProvider(new VariableLabelProvider());
//		this.stateTreeViewer.setInput(value);	
//		
//		setChecks(this.stateTreeViewer, STATE);
//
//		this.stateTreeViewer.refresh(true);
//	}
	
	private void setChecks(CheckboxTreeViewer treeViewer, String type){
		Tree tree = treeViewer.getTree();
		for(TreeItem item: tree.getItems()){
			setChecks(item, type);
		}
	}
	
	private void setChecks(TreeItem item, String type){
		Object element = item.getData();
		if(element == null){
			return;
		}
		
		Pair<TraceNode, VarValue> ev = (Pair<TraceNode, VarValue>)element;
		VarValue value = ev.second();
//		String varID = ev.getVarID();
		
		if(interesetedSelected.contains(ev)){
//		if(interestedVariables.contains(value)){
			item.setChecked(true);
			interesetedSelected.remove(ev);
		}
		else{
//			item.setGrayed(true);
			item.setChecked(false);
//			item.setChecked(false);
			
		}

		for(TreeItem childItem: item.getItems()){
			setChecks(childItem, type);
		}
	}
	


//	private void sortVars(List<VarValue> vars){
//		List<VarValue> readVars = vars;
//		Collections.sort(readVars, new Comparator<VarValue>() {
//			@Override
//			public int compare(VarValue o1, VarValue o2) {
//				return o1.getVarName().compareTo(o2.getVarName());
//			}
//		});
//	}
	private void sortVarValues(List<Pair<TraceNode, VarValue>> vars){
		Collections.sort(vars, new Comparator<Pair<TraceNode,VarValue>>() {
			@Override
			public int compare(final Pair<TraceNode,VarValue> o1, final Pair<TraceNode,VarValue> o2) {
				return o1.second().getLableByTarget(o1.first()).compareTo(o2.second().getLableByTarget(o2.first()));
			}
		});
	}
	
	public void refresh(TraceNode node, StepChangeType changeType, HashMap<TraceNode, List<Pair<TraceNode, VarValue>>> kept_data_edges,HashMap<TraceNode, List<TraceNode>> kept_ctl_edges, List<TraceNode> kept_nodes){
		this.currentNode = node;
		
		if(node != null){
			//BreakPointValue thisState = node.getProgramState();
			//createStateContent(thisState);
			
//			System.out.println(kept_data_edges);
			List<Pair<TraceNode,VarValue>> ReadVariables  = new ArrayList<>();
			if(kept_data_edges.keySet().contains(node)) {
				if(kept_data_edges.get(node)!=null)
					for(Pair<TraceNode, VarValue> dep: kept_data_edges.get(node)) 
						if(kept_nodes.contains(dep.first())) {
							ReadVariables.add(dep);							
						}
			}
			createReadVariableContect(node,ReadVariables, changeType);		
			sortVarValues(ReadVariables);
			
//			List<Pair<TraceNode,VarValue>> WrittenVariables  = new ArrayList<>();			
//			for(TraceNode usingNode: kept_nodes) {
//				if(kept_data_edges.get(usingNode)!=null) {
//					for(Pair<TraceNode, VarValue> dep: kept_data_edges.get(usingNode)) {
//						if(dep.first().equals(node)) {
//							if(kept_nodes.contains(dep.first())) {
//								WrittenVariables.add(dep);							
//							}
//						}
//					}
//				}
//			}			
//			createWrittenVariableContent(node,WrittenVariables, changeType);

			
			
			//original is below
//			sortVars(node.getReadVariables());
//			createReadVariableContect(node.getReadVariables(), changeType);			
//			sortVars(node.getWrittenVariables());			
//			createWrittenVariableContent(node.getWrittenVariables(), changeType, targetNode, edgeValue);
			
			
			this.controlButton.setSelection(false);
			this.dataButton.setSelection(false);
			if(changeType.getType()==StepChangeType.CTL){
				this.controlButton.setVisible(true);
				this.controlButton.setSelection(true);
			}
			else if(changeType.getType()==StepChangeType.DAT || changeType.getType()==StepChangeType.IDT || changeType.getType()==StepChangeType.SRCDAT){
				this.dataButton.setSelection(true);
				this.controlButton.setVisible(false);
			}
		}
		else{
			//createStateContent(null);
//			createWrittenVariableContent(null, null,changeType);
			List<Pair<TraceNode,VarValue>> ReadVariables  = new ArrayList<>();
			createReadVariableContect(null, ReadVariables,null);	
		}
		

		
		
	}

}
