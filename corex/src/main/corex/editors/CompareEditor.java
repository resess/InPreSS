package corex.editors;


import java.io.BufferedReader;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.Bullet;
import org.eclipse.swt.custom.CaretEvent;
import org.eclipse.swt.custom.CaretListener;
import org.eclipse.swt.custom.LineStyleEvent;
import org.eclipse.swt.custom.LineStyleListener;
import org.eclipse.swt.custom.ST;
import org.eclipse.swt.custom.SashForm;
import org.eclipse.swt.custom.StyleRange;
import org.eclipse.swt.custom.StyledText;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.GlyphMetrics;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Menu;
import org.eclipse.swt.widgets.MenuItem;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorSite;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.part.EditorPart;

import corex.StepChangeType;
import corex.StepChangeTypeChecker;
import corex.model.PairList;
import corex.model.TraceNodePair;
import corex.separatesnapshots.DiffMatcher;
import corex.separatesnapshots.diff.DiffChunk;
import corex.separatesnapshots.diff.FilePairWithDiff;
import corex.separatesnapshots.diff.LineChange;
import corex.views.CorexViews;
import microbat.model.BreakPoint;
import microbat.model.trace.Trace;
import microbat.model.trace.TraceNode;
import microbat.views.TraceView;

public class CompareEditor extends EditorPart {

	public static final String ID = "corex.editor.compare";
	
	private CompareTextEditorInput input;
	
	private StyledText newText;
	private StyledText oldText;
	
	private int selectedLine = -1;
	
	public CompareEditor() {
	}

	@Override
    public void init(IEditorSite site, IEditorInput input) throws PartInitException {
        if (!(input instanceof CompareTextEditorInput)) {
            throw new RuntimeException("Wrong input");
        }

        this.input = (CompareTextEditorInput) input;
        
        
//		TextFileDocumentProvider provider = new TextFileDocumentProvider();
//		setDocumentProvider(provider);
		
//      super.init(site, input);
        
        setSite(site);
        setInput(input);
        setPartName("Compare");
    }
	
	

	@Override
	public void createPartControl(Composite parent) {
		GridLayout parentLayout = new GridLayout();
		parentLayout.numColumns = 1;
		parent.setLayout(parentLayout);
		
		SashForm sashForm = new SashForm(parent, SWT.HORIZONTAL);
		GridData data = new GridData(SWT.FILL, SWT.FILL, true, true);
		sashForm.setLayoutData(data);
		
		sashForm.setLayout(new FillLayout());
		
//		GridLayout sashLayout = new GridLayout(2, true);
//		sashForm.setLayoutData(sashLayout);
		
		oldText = generateText(sashForm, input.getTargetFilePath(), input.getMatcher(), input.getPairList(), false, input.getOldTraceNode(), input.getOldKept());
		newText = generateText(sashForm, input.getSourceFilePath(), input.getMatcher(), input.getPairList(), true,  input.getNewTraceNode(), input.getNewKept());
		
		sashForm.setWeights(new int[]{50, 50});
	}

	public void highLight(TraceNode node) {
		input.setSelectedNode(node);
		
		TraceNode newNode = null;
		TraceNode oldNode = null;
		
		PairList list = input.getPairList();
		if(node.getBreakPoint().isSourceVersion()){//source means new version. 
			newNode = node;
			TraceNodePair pair = list.findByBeforeNode(node); //means in the old version
			if(pair != null){
				oldNode = pair.getAfterNode();
			}
		}
		else{
			oldNode = node;
			TraceNodePair pair = list.findByAfterNode(node); //means in the new version
			if(pair != null){
				newNode = pair.getBeforeNode();
			}
		}
		
		highlightStyles(true, newNode, newText, input.getMatcher(), input.getSourceFilePath());//source means new
		highlightStyles(false, oldNode, oldText, input.getMatcher(), input.getTargetFilePath());//target means old
		
		highlightKeptNodesStyles(true, newNode, newText, input.getMatcher(), input.getPairList(),input.getSourceFilePath(), input.getNewTraceNode(), input.getNewKept());
		highlightKeptNodesStyles(false, oldNode, oldText, input.getMatcher(), input.getPairList(), input.getTargetFilePath(), input.getOldTraceNode(), input.getOldKept());
		
		newText.redraw();
		oldText.redraw();
	}
	
	
	private void highlightStyles(boolean isNew, TraceNode node, StyledText text, DiffMatcher matcher, String path){
		List<StyleRange> ranges = new ArrayList<>();
		
		if(isNew){
			ranges = highlightSourceDiff(text, matcher, path);
			if(node != null){
				adjustTextForSelectedNode(node, text, ranges);	
			}
		}
		else{
			ranges = highlightTargetDiff(text, matcher, path);	
			if(node != null){
				adjustTextForSelectedNode(node, text, ranges);
			}
			
		}
		
		StyleRange[] rangeArray = sortList(ranges);
		appendLineStyle(text, rangeArray);
	}

	private void adjustTextForSelectedNode(TraceNode node, StyledText text, List<StyleRange> ranges) {
		int topLine = node.getLineNumber()-15;
		topLine = (topLine<1) ? 1 : topLine;
		text.setTopIndex(topLine);
		
		StyleRange selectedRange = selectedLineStyle(text, node.getLineNumber()); 
		ranges.add(selectedRange);
	}
	
	public StyledText generateText(SashForm sashForm, String path, DiffMatcher matcher, PairList pairList, final boolean isNew, List<TraceNode> trace_nodes, List<TraceNode> kept_nodes){
//		ScrolledComposite scrolledComp = new ScrolledComposite(sashForm, SWT.H_SCROLL | SWT.V_SCROLL);
//		scrolledComp.setExpandHorizontal(true);
//		scrolledComp.setExpandVertical(true);

		Composite composite = new Composite(sashForm, SWT.NONE);
		composite.setLayout(new GridLayout(1, true));
		
		Text label = new Text(composite, SWT.NONE);
		label.setText(path);
		label.setEditable(false);
		label.setLayoutData(new GridData(SWT.FILL, SWT.CENTER, true, false));
		
		final StyledText text = new StyledText(composite, 
				SWT.MULTI | SWT.LEAD | SWT.V_SCROLL | SWT.H_SCROLL);
		text.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
		text.setEditable(false);
		
		File file = new File(path);
		if(!file.exists()){
			path = path.replace(matcher.getSourceFolderName(), matcher.getTestFolderName());
			file = new File(path);
		}
		
		String content = parseSourceContent(file);
		text.setText(content);
		
		//gray out the statements that are not kept but the technique
		highlightKeptNodesStyles(isNew, null, text, matcher, pairList, path, trace_nodes, kept_nodes);
		
//		highlightStyles(isNew, null, text, matcher, path);
		
		Menu popupMenu = generatePopMenu(isNew, text);
		text.setMenu(popupMenu);
		text.addCaretListener(new CaretListener() {
			
			@Override
			public void caretMoved(CaretEvent event) {
				int offset = event.caretOffset;
				int lineNumber = text.getLineAtOffset(offset);
				selectedLine = lineNumber + 1;
			}
		});
		
//		scrolledComp.setContent(composite);
//		scrolledComp.setMinSize(composite.computeSize(SWT.DEFAULT, SWT.DEFAULT));
		
		return text;
	}

	private void highlightKeptNodesStyles(boolean isNew, TraceNode node, StyledText text, DiffMatcher matcher,
			PairList pairList, String path, List<TraceNode> trace_nodes, List<TraceNode> kept_nodes) {
		List<StyleRange> ranges = new ArrayList<>();
		
		
		ranges = highlightkeptNodes(isNew, text, matcher, pairList, path, trace_nodes, kept_nodes);
		if(node != null){
			adjustTextForSelectedNode(node, text, ranges);	
		}
				
		StyleRange[] rangeArray = sortList(ranges);
		appendLineStyle(text, rangeArray);
		
	}

	private List<StyleRange> highlightkeptNodes(boolean isNew, StyledText text, DiffMatcher matcher, PairList pairList, String path,
			List<TraceNode> trace_nodes, List<TraceNode> kept_nodes) {
		List<StyleRange> ranges = new ArrayList<>();
		
		List<Integer> visited = new ArrayList<>();
		for(TraceNode node: trace_nodes){//for executed ones
			if (path.equals(node.getBreakPoint().getFullJavaFilePath())){
				visited.add(node.getLineNumber());//for the not executed ones in the file to make them grey
				if (kept_nodes.contains(node)) {
					boolean isSourceDiff = matcher.checkSourceDiff(node.getBreakPoint(), isNew);
					if(isSourceDiff) {
						StyleRange range = new StyleRange();
						range.start = text.getOffsetAtLine(node.getLineNumber()-1); //the offset of the first character in the line
						String content = getJustSourceCode(node, isNew, matcher);
						range.length = content.length();
						range.foreground = Display.getCurrent().getSystemColor(SWT.COLOR_RED);
						range.background = new Color(Display.getCurrent(), 255, 247, 248);
						ranges.add(range);
					}
					else {	
						StyleRange range = new StyleRange();
						range.start = text.getOffsetAtLine(node.getLineNumber()-1);
						String content = getJustSourceCode(node, isNew, matcher);
						range.length = content.length();
						range.foreground = Display.getCurrent().getSystemColor(SWT.COLOR_BLACK);
						range.background = new Color(Display.getCurrent(), 211, 211, 211);
						ranges.add(range);
					}
				}
				else {
//					System.out.println("it is not kept");
					StyleRange range = new StyleRange();
					range.start = text.getOffsetAtLine(node.getLineNumber()-1);
					String content = getJustSourceCode(node, isNew, matcher);
					range.length = content.length();
					range.foreground = Display.getCurrent().getSystemColor(SWT.COLOR_GRAY);
//					range.background = new Color(Display.getCurrent(), 255, 247, 248);
					ranges.add(range);
				}
			}			
		}
		
		File file = new File(path);		
		if(file.exists()){
			InputStream stdin;
			try {
				stdin = new FileInputStream(file);
				InputStreamReader isr = new InputStreamReader(stdin);
				BufferedReader br = new BufferedReader(isr);

				String line = null;
				int index = 1;
				while ( (line = br.readLine()) != null){						
					if(!visited.contains(index)) {//not executed line
						StyleRange range = new StyleRange();
						range.start = text.getOffsetAtLine(index-1);
						range.length = line.length();
						range.foreground = Display.getCurrent().getSystemColor(SWT.COLOR_GRAY);
	//					range.background = new Color(Display.getCurrent(), 255, 247, 248);
						ranges.add(range);
					}
					index++;					
				}				
			} catch (FileNotFoundException e1) {
				e1.printStackTrace();
			} catch (IOException e1) {
				e1.printStackTrace();
			}
		}
		
		return ranges;
	}
public String getJustSourceCode(TraceNode traceNode, boolean isOnNew, DiffMatcher matcher) {
		
		int lineNo = traceNode.getLineNumber();	
		String source = null;
        BreakPoint breakPoint = traceNode.getBreakPoint();
        String Path = breakPoint.getFullJavaFilePath();
		File file = new File(Path);
//		if(!file.exists()){
//			path = path.replace(matcher.getSourceFolderName(), matcher.getTestFolderName());
//			file = new File(path);
//		}
		
		if(file.exists()){
			InputStream stdin;
			try {
				stdin = new FileInputStream(file);
				InputStreamReader isr = new InputStreamReader(stdin);
				BufferedReader br = new BufferedReader(isr);

				String line = null;
				int index = 1;
				while ( (line = br.readLine()) != null){					
					if(index==lineNo) {
						source = line;
						return source;
					}
					index++;
				}				
			} catch (FileNotFoundException e1) {
				e1.printStackTrace();
			} catch (IOException e1) {
				e1.printStackTrace();
			}
		}
		return source;
		
		
		
	}
	private Menu generatePopMenu(final boolean isNew, final StyledText text) {
		Menu popupMenu = new Menu(text);
	    MenuItem forwardItem = new MenuItem(popupMenu, SWT.CASCADE);
	    forwardItem.setText("Search Previous Step");
		forwardItem.addSelectionListener(new SelectionListener() {
			
			@Override
			public void widgetSelected(SelectionEvent e) {
				String className = input.getSelectedNode().getClassCanonicalName();
				int lineNumber = selectedLine;
				
				String expression = Trace.combineTraceNodeExpression(className, lineNumber);
				
				TraceView traceView = isNew? 
						CorexViews.getNewTraceView() : CorexViews.getOldTraceView();
				traceView.setSearchText(expression);
				traceView.jumpToNode(expression, false);
			}
			
			@Override
			public void widgetDefaultSelected(SelectionEvent e) {
				
			}
		});
		
		MenuItem backwardItem = new MenuItem(popupMenu, SWT.CASCADE);
	    backwardItem.setText("Search Next Steps");
		backwardItem.addSelectionListener(new SelectionListener() {
			
			@Override
			public void widgetSelected(SelectionEvent e) {
				String className = input.getSelectedNode().getClassCanonicalName();
				int lineNumber = selectedLine;
				
				String expression = Trace.combineTraceNodeExpression(className, lineNumber);
				
				TraceView traceView = isNew? 
						CorexViews.getNewTraceView() : CorexViews.getOldTraceView();
				traceView.setSearchText(expression);
				traceView.jumpToNode(expression, true);
			}
			
			@Override
			public void widgetDefaultSelected(SelectionEvent e) {
				
			}
		});
		
		
		
		return popupMenu;
	}
	
	/**
	 * Bubble sort
	 * @return
	 */
	private StyleRange[] sortList(List<StyleRange> ranges){
		StyleRange[] rangeArray = ranges.toArray(new StyleRange[0]);
		for(int i=0; i<rangeArray.length; i++){
			for(int j=1; j<rangeArray.length-i; j++){
				int prev = rangeArray[j-1].start;
				int post = rangeArray[j].start;
				if(prev > post){
					StyleRange temp = rangeArray[j];
					rangeArray[j] = rangeArray[j-1];
					rangeArray[j-1] = temp;
				}
			}
		}
		
		System.currentTimeMillis();
		
		return rangeArray;
	}
	
	private StyleRange selectedLineStyle(StyledText text, int line){
		StyleRange range = new StyleRange();
		range.start = text.getOffsetAtLine(line-1);
		range.length = text.getOffsetAtLine(line)-range.start;
		range.foreground = Display.getCurrent().getSystemColor(SWT.COLOR_BLUE);
		range.background = new Color(Display.getCurrent(), 230, 255, 255);
		range.fontStyle = SWT.BOLD;
		
		return range;
	}

	private List<StyleRange> highlightSourceDiff(StyledText text, DiffMatcher matcher, String path) {
		
		List<StyleRange> ranges = new ArrayList<>();
		
		FilePairWithDiff diff = matcher.findDiffBySourceFile(path);
		
		if(diff==null){
			return ranges;
		}
		
		for(DiffChunk chunk: diff.getChunks()){
			int currentLine = chunk.getStartLineInSource();
			for(LineChange line: chunk.getChangeList()){
				if(line.getLineContent().startsWith("-")){
					StyleRange range = new StyleRange();
					range.start = text.getOffsetAtLine(currentLine-1);
					String content = line.getLineContent();
					range.length = content.length();
					range.foreground = Display.getCurrent().getSystemColor(SWT.COLOR_RED);
					range.background = new Color(Display.getCurrent(), 255, 247, 248);
					
					ranges.add(range);
				}
				
				if(!line.getLineContent().startsWith("+")){
					currentLine++;					
				}
			}
		}
		
		return ranges;
		
	}
	
	private List<StyleRange> highlightTargetDiff(StyledText text, DiffMatcher matcher, String path) {
		List<StyleRange> ranges = new ArrayList<>();
		FilePairWithDiff diff = matcher.findDiffByTargetFile(path);
		
		if(diff==null){
			return ranges;
		}
		
		for(DiffChunk chunk: diff.getChunks()){
			int currentLine = chunk.getStartLineInTarget();
			for(LineChange line: chunk.getChangeList()){
				if(line.getLineContent().startsWith("+")){
					StyleRange range = new StyleRange();
					range.start = text.getOffsetAtLine(currentLine-1);
					String content = line.getLineContent();
					range.length = content.length()-range.start;
					range.foreground = Display.getCurrent().getSystemColor(SWT.COLOR_RED);
					range.background = new Color(Display.getCurrent(), 255, 247, 248);
					
					ranges.add(range);
				}
				
				if(!line.getLineContent().startsWith("-")){
					currentLine++;					
				}
			}
		}
		
		return ranges;
		
	}

	class CusLineStyleListener implements LineStyleListener{

		private StyledText text;
		private StyleRange[] ranges;
		
		
		public CusLineStyleListener(StyledText text, StyleRange[] ranges) {
			super();
			this.text = text;
			this.ranges = ranges;
		}

		@Override
		public void lineGetStyle(LineStyleEvent e) {
			e.bulletIndex = text.getLineAtOffset(e.lineOffset);
	        e.styles = ranges;
	        
	        //Set the style, 12 pixles wide for each digit
	        StyleRange style = new StyleRange();
	        style.foreground = Display.getCurrent().getSystemColor(SWT.COLOR_DARK_GRAY);
	        style.metrics = new GlyphMetrics(0, 0, Integer.toString(text.getLineCount()+1).length()*12);

	        //Create and set the bullet
	        e.bullet = new Bullet(ST.BULLET_NUMBER, style);
			
		}
		
	}
	
	private CusLineStyleListener styleListener;
//	private JavaLineStyler javaLineStyler;
	
	private void appendLineStyle(StyledText text, StyleRange[] ranges) {
//		JavaLineStyler javaLineStyler = new JavaLineStyler();
//		text.addLineStyleListener(javaLineStyler);
		
		if(this.styleListener != null){
			text.removeLineStyleListener(this.styleListener);	
		}
		
		this.styleListener = new CusLineStyleListener(text, ranges);
		text.addLineStyleListener(this.styleListener);
		
	}

	@SuppressWarnings("resource")
	private String parseSourceContent(File file) {
		String content = "";
		if(file.exists()){
			InputStream stdin;
			try {
				stdin = new FileInputStream(file);
				InputStreamReader isr = new InputStreamReader(stdin);
				BufferedReader br = new BufferedReader(isr);
				
				StringBuffer buffer = new StringBuffer();
				String line = null;
				while ( (line = br.readLine()) != null){
					buffer.append(line);
					buffer.append('\n');
				}
				
				content = buffer.toString();
			} catch (FileNotFoundException e1) {
				e1.printStackTrace();
			} catch (IOException e1) {
				e1.printStackTrace();
			}
		}
		return content;
	}

	@Override
	public void doSave(IProgressMonitor monitor) {
		
	}

	@Override
	public void doSaveAs() {
		
	}

	@Override
	public boolean isDirty() {
		return false;
	}

	@Override
	public boolean isSaveAsAllowed() {
		return false;
	}

	@Override
	public void setFocus() {
		
	}

}
