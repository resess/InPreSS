package corex.editors;

import java.util.List;

import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IPersistableElement;

import corex.model.PairList;
import corex.separatesnapshots.DiffMatcher;
import microbat.model.trace.Trace;
import microbat.model.trace.TraceNode;

public class CompareTextEditorInput implements IEditorInput {

	private TraceNode selectedNode;
	private List<TraceNode> new_trace_kept;
	private List<TraceNode> old_trace_kept;
	private List<TraceNode> new_trace_nodes;
	private List<TraceNode> old_trace_nodes;
	private Trace new_trace;
	private Trace old_trace;
	private PairList pairList;
	
	private String sourceFilePath;
	private String targetFilePath;

	private DiffMatcher matcher;

	public CompareTextEditorInput(TraceNode selectedNode, PairList pairList, String sourceFilePath,
			String targetFilePath, DiffMatcher matcher, Trace new_trace, Trace old_trace, List<TraceNode> new_list, List<TraceNode> old_list, List<TraceNode> new_kept, List<TraceNode> old_kept ) {
		super();
		this.setSelectedNode(selectedNode);
		this.setPairList(pairList);
		this.sourceFilePath = sourceFilePath;
		this.targetFilePath = targetFilePath;
		this.matcher = matcher;
		this.new_trace_kept = new_kept;
		this.old_trace_kept = old_kept;
		this.new_trace_nodes = new_list;
		this.old_trace_nodes = old_list;
		this.new_trace = new_trace;
		this.old_trace = old_trace;
	}
	
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((sourceFilePath == null) ? 0 : sourceFilePath.hashCode());
		result = prime * result + ((targetFilePath == null) ? 0 : targetFilePath.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		CompareTextEditorInput other = (CompareTextEditorInput) obj;
		if (sourceFilePath == null) {
			if (other.sourceFilePath != null)
				return false;
		} else if (!sourceFilePath.equals(other.sourceFilePath))
			return false;
		if (targetFilePath == null) {
			if (other.targetFilePath != null)
				return false;
		} else if (!targetFilePath.equals(other.targetFilePath))
			return false;
		return true;
	}

	public DiffMatcher getMatcher() {
		return matcher;
	}
	public List<TraceNode> getOldKept() {
		return old_trace_kept;
	}
	public List<TraceNode> getNewKept() {
		return new_trace_kept;
	}
	public List<TraceNode> getNewTraceNode() {
		return new_trace_nodes;
	}
	public List<TraceNode> getOldTraceNode() {
		return old_trace_nodes;
	}
	public Trace getNewTrace() {
		return new_trace;
	}
	public Trace getOldTrace() {
		return old_trace;
	}

	public void setMatcher(DiffMatcher matcher) {
		this.matcher = matcher;
	}

	public String getSourceFilePath() {
		return sourceFilePath;
	}

	public void setSourceFilePath(String sourceFilePath) {
		this.sourceFilePath = sourceFilePath;
	}

	public String getTargetFilePath() {
		return targetFilePath;
	}

	public void setTargetFilePath(String targetFilePath) {
		this.targetFilePath = targetFilePath;
	}

	@Override
	public <T> T getAdapter(Class<T> adapter) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public boolean exists() {
		return true;
	}

	@Override
	public ImageDescriptor getImageDescriptor() {
		return null;
	}

	@Override
	public String getName() {
		return "compare";
	}

	@Override
	public IPersistableElement getPersistable() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public String getToolTipText() {
		// TODO Auto-generated method stub
		return null;
	}

	public TraceNode getSelectedNode() {
		return selectedNode;
	}

	public void setSelectedNode(TraceNode selectedNode) {
		this.selectedNode = selectedNode;
	}

	public PairList getPairList() {
		return pairList;
	}

	public void setPairList(PairList pairList) {
		this.pairList = pairList;
	}

}
