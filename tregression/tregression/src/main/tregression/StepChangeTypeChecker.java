package tregression;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import com.google.common.collect.BiMap;
import com.google.common.collect.HashBiMap;

import microbat.model.trace.Trace;
import microbat.model.trace.TraceNode;
import microbat.model.value.ReferenceValue;
import microbat.model.value.VarValue;
import microbat.model.value.VirtualValue;
import microbat.model.variable.ArrayElementVar;
import microbat.model.variable.Variable;
import microbat.model.variable.VirtualVar;
import microbat.util.PrimitiveUtils;
import sav.common.core.Pair;
import tregression.empiricalstudy.MatchStepFinder;
import tregression.model.PairList;
import tregression.model.TraceNodePair;
import tregression.separatesnapshots.DiffMatcher;

public class StepChangeTypeChecker {
	
	private Trace buggyTrace;
	private Trace correctTrace;

	BiMap<TraceNode, String> newSlicer4J = HashBiMap.create();
	BiMap<TraceNode, String> oldSlicer4J = HashBiMap.create();
	HashMap<String, List<String>> newSlicer4JBytecodeMapping = new HashMap<>();
	HashMap<String, List<String>> oldSlicer4JBytecodeMapping = new HashMap<>();

	public StepChangeTypeChecker(Trace buggyTrace, Trace correctTrace, String proPath, BiMap<TraceNode, String> newSlicer4J, HashMap<String, List<String>> newSlicer4JBytecodeMapping, BiMap<TraceNode, String> oldSlicer4J, HashMap<String, List<String>> oldSlicer4JBytecodeMapping) throws IOException {
		super();
		this.setBuggyTrace(buggyTrace);
		this.setCorrectTrace(correctTrace);

        this.newSlicer4J = newSlicer4J;
        this.oldSlicer4J = oldSlicer4J;
        this.newSlicer4JBytecodeMapping = newSlicer4JBytecodeMapping;
        this.oldSlicer4JBytecodeMapping = oldSlicer4JBytecodeMapping;

	}
	public StepChangeTypeChecker(Trace buggyTrace, Trace correctTrace){
		super();
		this.setBuggyTrace(buggyTrace);
		this.setCorrectTrace(correctTrace);
	}
	/**
	 * By default, buggy code is the before/source and the correct code is the
	 * after/target. This convention corresponds to the UI design and defects4j
	 * patches.
	 * 
	 * @param step
	 * @param isOnNewTrace
	 * @param pairList
	 * @param matcher
	 * @return
	 */
////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////
	public StepChangeType getType(TraceNode step, boolean isOnNewTrace,
			PairList pairList, DiffMatcher matcher) {
		TraceNode matchedStep = null;
	
			 matchedStep = MatchStepFinder.findMatchedStep(isOnNewTrace, step, pairList);
		

		///////////////////////////////////////////////////////////////////////////////////
		
		
		boolean isSourceDiff = matcher.checkSourceDiff(step.getBreakPoint(), isOnNewTrace);
		if(isSourceDiff){
			return new StepChangeType(StepChangeType.SRC, matchedStep);			
		}
		if (matchedStep == null ) {
			return new StepChangeType(StepChangeType.CTL, matchedStep);
			
		}
		else{
			List<Pair<VarValue, VarValue>> wrongVariableList = checkWrongVariable(isOnNewTrace, step, matchedStep, pairList, matcher);
			//List<Pair<VarValue, VarValue>> DefWrongVariableList = checkDefWrongVariable(isOnNewTrace, step, matchedStep, pairList, matcher);			
			//if(wrongVariableList.isEmpty() && DefWrongVariableList.isEmpty()){
			if(wrongVariableList.isEmpty() ){	
				return new StepChangeType(StepChangeType.IDT, matchedStep);
			}
			else{
				return new StepChangeType(StepChangeType.DAT, matchedStep, wrongVariableList);
			}
			
		}

	}
////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////	
	public StepChangeType getTypeForPrinting(TraceNode step, boolean isOnNewTrace, 
			PairList pairList, DiffMatcher matcher) {
		
		
		TraceNode matchedStep = null;
//		if(newSlicer4J.size()==0) {	

			 matchedStep = MatchStepFinder.findMatchedStep(isOnNewTrace, step, pairList);
//		}
//		else {
//			
//			 matchedStep = findMatchedStepwithStringTraceAlignment(isOnNewTrace, step);
//		}
		
		boolean isSourceDiff = matcher.checkSourceDiff(step.getBreakPoint(), isOnNewTrace);
	
		if (matchedStep == null ) {
			if(isSourceDiff) {			
				return new StepChangeType(StepChangeType.SRCCTL, matchedStep);
			}
			else {
				
				return new StepChangeType(StepChangeType.CTL, matchedStep);	
			}
		}
		else{
			List<Pair<VarValue, VarValue>> wrongVariableList = checkWrongVariable(isOnNewTrace, step, matchedStep, pairList, matcher);
			List<Pair<VarValue, VarValue>> DefWrongVariableList = checkDefWrongVariable(isOnNewTrace, step, matchedStep, pairList, matcher);
			
			if(wrongVariableList.isEmpty() && DefWrongVariableList.isEmpty()){
			
				return new StepChangeType(StepChangeType.IDT, matchedStep);
			}
			else{
				if(isSourceDiff) {					
					return new StepChangeType(StepChangeType.SRCDAT, matchedStep, wrongVariableList);
				}
				else {
			
					return new StepChangeType(StepChangeType.DAT, matchedStep, wrongVariableList);
				}
			}
		}

	}
////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////
//	private TraceNode findMatchedStepwithStringTraceAlignment(boolean isOnNewTrace, TraceNode step) {
//		if(isOnNewTrace) {
//			List<Integer> positions = dualSlicingWithSlicer4J.getSlicer4JMappedNode(step, newSlicer4J, newSlicer4JBytecodeMapping);
//			if (positions!=null) {
//				for(Integer pos: positions) {
//					Integer mathcedPos = traceAlign.getMatchOfSecondToFirst(pos.intValue());
//					if (mathcedPos!=null) {
//						StatementInstance stmt = this.oldDcfg.mapNoUnits(mathcedPos);
//						TraceNode matchedNode = dualSlicingWithSlicer4J.getTraceNodeMapping(stmt, oldSlicer4J, oldSlicer4JBytecodeMapping);
//					    if (matchedNode!=null)
//					    	return matchedNode;
//					}
//				}
//			}
//		}
//		else {
//			List<Integer> positions = dualSlicingWithSlicer4J.getSlicer4JMappedNode(step, oldSlicer4J, oldSlicer4JBytecodeMapping);
//			if (positions!=null) {
//				for(Integer pos: positions) {
//					Integer mathcedPos = traceAlign.getMatchOfFirstToSecond(pos.intValue());
//					if (mathcedPos!=null) {
//						StatementInstance stmt =  this.newDcfg.mapNoUnits(mathcedPos);
//						TraceNode matchedNode = dualSlicingWithSlicer4J.getTraceNodeMapping(stmt, newSlicer4J, newSlicer4JBytecodeMapping);
//					    if (matchedNode!=null)
//					    	return matchedNode;
//					}
//				}
//			}
//		}   
//		return null;
//	}
////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////
	private List<Pair<VarValue, VarValue>> checkDefWrongVariable(boolean isOnBefore,
			TraceNode thisStep, TraceNode thatStep, PairList pairList, DiffMatcher matcher) {
	
		List<Pair<VarValue, VarValue>> wrongVariableList = new ArrayList<>();
		int count = 0;
		for(VarValue readVar: thisStep.getWrittenVariables()){
			
		
			
			VarMatch varMatch = DefCanbeMatched(isOnBefore, readVar, thisStep, thatStep, pairList, matcher);
//			System.currentTimeMillis();
			if(varMatch.canBeMatched && !varMatch.sameContent){
				if(isOnBefore){
					Pair<VarValue, VarValue> pair = Pair.of(readVar, varMatch.matchedVariable);
					wrongVariableList.add(pair);
				}
				else{
					Pair<VarValue, VarValue> pair = Pair.of(varMatch.matchedVariable, readVar);
					wrongVariableList.add(pair);
				}
			}
		}
		
		return wrongVariableList;
	}

	private VarMatch DefCanbeMatched(boolean isOnBeforeTrace, 
			VarValue thisVar, TraceNode thisStep, TraceNode thatStep, PairList pairList, DiffMatcher matcher) {
		Trace thisTrace = getCorrespondingTrace(isOnBeforeTrace, buggyTrace, correctTrace);
		Trace thatTrace = getOtherCorrespondingTrace(isOnBeforeTrace, buggyTrace, correctTrace);
		
		List<VarValue> synonymVarList = findDefSynonymousVarList(thisStep, thatStep, thisVar, 
				isOnBeforeTrace, pairList, matcher);
		if(synonymVarList.isEmpty()){
			return new VarMatch(false, false, null);
		}
		
		VarValue matchedVar = null;
		for(VarValue thatVar: synonymVarList){
			matchedVar = thatVar;
			
			
				String thisString = (thisVar.getStringValue()==null)?"null":thisVar.getStringValue();
				String thatString = (thatVar.getStringValue()==null)?"null":thatVar.getStringValue();
				
				boolean equal = thisString.equals(thatString);
				if(isIgnoreVarName(thisVar.getVarName()) && isIgnoreVarName(thatVar.getVarName())){
					equal = true;
				}
				
				if(!equal) {
					matchedVar = thatVar;
					continue;
				}
				else {
					return new VarMatch(true, true, thatVar);					
				}
			
		}
		
		
		return new VarMatch(true, false, matchedVar);
	}

	private List<VarValue> findDefSynonymousVarList(TraceNode thisStep, TraceNode thatStep, VarValue thisVar,
			boolean isOnBeforeTrace, PairList pairList, DiffMatcher matcher) {
		List<VarValue> writtenVariables = thatStep.getWrittenVariables();
		List<VarValue> synonymousList = new ArrayList<>();
		for(VarValue writtenVar: writtenVariables) {
				if(writtenVar.getVariable() instanceof VirtualVar && thisVar.getVariable() instanceof VirtualVar){
					String virName1 = writtenVar.getVarName();
					String virName2 = thisVar.getVarName();
					
					String simpleName1 = virName1.substring(virName1.lastIndexOf("#"), virName1.length());
					String simpleName2 = virName2.substring(virName2.lastIndexOf("#"), virName2.length());
					
					if(simpleName1.equals(simpleName2)){
						synonymousList.add(writtenVar);
					}
				}
				else if(writtenVar.getVarName().equals(thisVar.getVarName())) {
					synonymousList.add(writtenVar);
				}
			
		}
		return synonymousList;
	}


	
	/**
	 * When invoking a method m() at line k, we will have two steps running into line k, i.e., a step s_1 
	 * invoking m() and a step s_2 returning from the invocation. Suppose s_1 is matched and s_2 is not, 
	 * we should not check s_2's control dominator, instead, we need to check s_1 instead.
	 * 
	 * In this implementation, we only consider case of non-cascading invocation. In other word, we do not
	 * consider m0(m1(m2(...))). In such case, we need to consider a list of previous-step-over-step.
	 * @param step
	 * @return
	 */
	private TraceNode findPreviousStepOverStepWithSameLine(TraceNode step) {
		TraceNode node = step.getStepOverPrevious();
		if(node != null && node.getLineNumber()==step.getLineNumber()) {
			return node;
		}
		
		return null;
	}

	private List<Pair<VarValue, VarValue>> checkWrongVariable(boolean isOnBefore,
			TraceNode thisStep, TraceNode thatStep, PairList pairList, DiffMatcher matcher) {
		List<Pair<VarValue, VarValue>> wrongVariableList = new ArrayList<>();
		int count = 0;
		for(VarValue readVar: thisStep.getReadVariables()){
			count++;
			//if(count>100){
				//break;
			//}
			
			VarMatch varMatch = canbeMatched(isOnBefore, readVar, thisStep, thatStep, pairList, matcher);
//			System.currentTimeMillis();
			if(varMatch.canBeMatched && !varMatch.sameContent){
				if(isOnBefore){
					Pair<VarValue, VarValue> pair = Pair.of(readVar, varMatch.matchedVariable);
					wrongVariableList.add(pair);
				}
				else{
					Pair<VarValue, VarValue> pair = Pair.of(varMatch.matchedVariable, readVar);
					wrongVariableList.add(pair);
				}
			}
		}
		
		return wrongVariableList;
	}
	
	private Trace getCorrespondingTrace(boolean isOnBeforeTrace, Trace buggyTrace, Trace correctTrace) {
		return isOnBeforeTrace ? buggyTrace : correctTrace;
	}
	
	private Trace getOtherCorrespondingTrace(boolean isOnBeforeTrace, Trace buggyTrace, Trace correctTrace) {
		return !isOnBeforeTrace ? buggyTrace : correctTrace;
	}
	
	class VarMatch{
		VarValue matchedVariable;
		boolean canBeMatched;
		
		/**
		 * can find the matched variable
		 */
		boolean sameContent;
		public VarMatch(boolean canBeMatched, boolean sameVariable, VarValue matchedVariable) {
			super();
			this.canBeMatched = canBeMatched;
			this.sameContent = sameVariable;
			this.matchedVariable = matchedVariable;
		}
		
	}

	private VarMatch canbeMatched(boolean isOnBeforeTrace, 
			VarValue thisVar, TraceNode thisStep, TraceNode thatStep, PairList pairList, DiffMatcher matcher) {
		Trace thisTrace = getCorrespondingTrace(isOnBeforeTrace, buggyTrace, correctTrace);
		Trace thatTrace = getOtherCorrespondingTrace(isOnBeforeTrace, buggyTrace, correctTrace);
//		boolean containsVirtual = checkReturnVariable(thisStep, thatStep);
		
		List<VarValue> synonymVarList = findSynonymousVarList(thisStep, thatStep, thisVar, 
				isOnBeforeTrace, pairList, matcher);
		if(synonymVarList.isEmpty()){
			return new VarMatch(false, false, null);
		}
		
		VarValue matchedVar = null;
		for(VarValue thatVar: synonymVarList){
			matchedVar = thatVar;
			
			TraceNode thisDom = thisTrace.findDataDependency(thisStep, thisVar);
			TraceNode thatDom = thatTrace.findDataDependency(thatStep, thatVar);
			if(thatVar instanceof ReferenceValue && thisVar instanceof ReferenceValue) {
				boolean isReferenceValueMatch = isReferenceValueMatch((ReferenceValue)thisVar, (ReferenceValue)thatVar, 
						thisDom, thatDom, isOnBeforeTrace, pairList, matcher);
				if(isReferenceValueMatch){
					return new VarMatch(true, true, thatVar);
				}
			}
			else {
				String thisString = (thisVar.getStringValue()==null)?"null":thisVar.getStringValue();
				String thatString = (thatVar.getStringValue()==null)?"null":thatVar.getStringValue();
				
				boolean equal = thisString.equals(thatString);
				if(isIgnoreVarName(thisVar.getVarName()) && isIgnoreVarName(thatVar.getVarName())){
					equal = true;
				}
				
				if(!equal) {
					matchedVar = thatVar;
					continue;
				}
				else {
					return new VarMatch(true, true, thatVar);					
				}
			}
		}
		
		
		return new VarMatch(true, false, matchedVar);
	}

	@SuppressWarnings({ "rawtypes" })
	private boolean isReferenceValueMatch(ReferenceValue thisVar, ReferenceValue thatVar, TraceNode thisDom, TraceNode thatDom,
			boolean isOnBeforeTrace, PairList pairList, DiffMatcher matcher) {
		
		List<TraceNode> thisAssignChain = new ArrayList<>();
		getAssignChain(thisDom, thisVar, thisAssignChain);
		List<TraceNode> thatAssignChain = new ArrayList<>(); 
		getAssignChain(thatDom, thatVar, thatAssignChain);
		
		boolean isAssignChainMatch = isAssignChainMatch(thisAssignChain, thatAssignChain, isOnBeforeTrace, pairList, matcher);
		
		boolean isContentMatch = true;
		if(!thisVar.getStringValue().contains("@")){
			String thisType = thisVar.getType();
			String thatType = thatVar.getType();
			if(!PrimitiveUtils.isPrimitiveTypeOrString(thisType) 
					&& !PrimitiveUtils.isPrimitiveTypeOrString(thatType)){
				try {
					Class thisClass = Class.forName(thisType);
					Class thatClass = Class.forName(thatType);
					
					if(java.util.Collection.class.isAssignableFrom(thisClass) ||
							java.util.Collection.class.isAssignableFrom(thatClass) ||
							java.util.Map.class.isAssignableFrom(thisClass) ||
							java.util.Map.class.isAssignableFrom(thatClass)){
						isContentMatch = true;
					}
					else{
						isContentMatch = thisVar.getStringValue().equals(thatVar.getStringValue());
//						isContentMatch = true;
					}
					
				} catch (ClassNotFoundException e) {
					isContentMatch = thisVar.getStringValue().equals(thatVar.getStringValue());
//					isContentMatch = true;
				}
				
				if(isIgnoreType(thisType) && isIgnoreType(thatType)){
					isContentMatch = true;
				}
				
//				if(thisVar.getVarName().equals("this") && thatVar.getVarName().equals("this")){
//					isContentMatch = true;
//				}
			}
			else{
				if(isIgnoreVarName(thisVar.getVarName()) && isIgnoreVarName(thatVar.getVarName())){
					isContentMatch = true;
				}
				else{
					isContentMatch = thisVar.getStringValue().equals(thatVar.getStringValue());									
				}
			}
		}
		else{
			String thisType = thisVar.getStringValue().substring(0, thisVar.getStringValue().indexOf("@"));
			if(!thatVar.getStringValue().contains("@")){
				isContentMatch = false;
			}
			else{
				String thatType = thatVar.getStringValue().substring(0, thatVar.getStringValue().indexOf("@"));
				if(!thisType.equals(thatType)){
					isContentMatch = false;
				}
			}
		}
		
		return isAssignChainMatch && isContentMatch;
	}
	
	private boolean isIgnoreVarName(String varName){
		return varName.contains("java.util.HashMap#hash") 
				|| varName.contains("java.util.HashMap#indexFor");
	}

	private boolean isIgnoreType(String thisType) {
		return thisType.contains("StopWatch") ||
				thisType.contains("StringBuffer");
	}

	private boolean isAssignChainMatch(List<TraceNode> thisAssignChain, List<TraceNode> thatAssignChain,
			boolean isOnBeforeTrace, PairList pairList, DiffMatcher matcher) {
		if(thisAssignChain.size() != thatAssignChain.size()){
			return false;
		}
		
		if(!isOnBeforeTrace){
			List<TraceNode> tmp = null;
			tmp = thisAssignChain;
			thisAssignChain = thatAssignChain;
			thatAssignChain = tmp;
		}
		
		for(int i=0; i<thisAssignChain.size(); i++){
			TraceNode thisDom = thisAssignChain.get(i);
			TraceNode thatDom = thatAssignChain.get(i);
			
			TraceNodePair pair = pairList.findByAfterNode(thatDom);
			if(pair==null){
				return false;
			}
			
			if(pair.getBeforeNode()==null){
				return false;
			}
			
			if(thisDom.getOrder()!=pair.getBeforeNode().getOrder()){
				return false;
			}
			
			if(thisDom.getOrder()==pair.getBeforeNode().getOrder()){
				boolean isThisDiff = matcher.checkSourceDiff(thisDom.getBreakPoint(), true);
				boolean isThatDiff = matcher.checkSourceDiff(thatDom.getBreakPoint(), false);
				
				if(isThisDiff || isThatDiff){
					return false;
				}
				
//				StepChangeType t1 = getType(thisDom, thisDom.getBreakPoint().isSourceVersion(), pairList, matcher);
//				if(t1.getType()!=StepChangeType.IDT){
//					return false;
//				}
//				
//				StepChangeType t2 = getType(thatDom, thatDom.getBreakPoint().isSourceVersion(), pairList, matcher);
//				if(t2.getType()!=StepChangeType.IDT){
//					return false;
//				}
			}
		}

		return true;
	}

	private void getAssignChain(TraceNode dom, VarValue var, List<TraceNode> chain) {
		if(dom==null){
			return;
		}
		
		chain.add(dom);
		
		String address = Variable.truncateSimpleID(var.getAliasVarID());
		for(VarValue readVar: dom.getReadVariables()){
			String readVarID = readVar.getAliasVarID();
			if(readVarID==null){
				continue;
			}
			
			String readAddress = Variable.truncateSimpleID(readVarID);
			if(address!=null && address.equals(readAddress)){
				TraceNode newDom = dom.getDataDominator(readVar);
				if(!chain.contains(newDom)){
					getAssignChain(newDom, readVar, chain);					
				}
				break;
			}
		}
	}
	
	private VarValue findReadParentVariable(ReferenceValue parent, TraceNode step) {
		for(VarValue readVar: step.getReadVariables()){
			if(readVar.getAliasVarID()==null){
				continue;
			}
			
			if(readVar.getAliasVarID().equals(parent.getVarID())){
				return readVar;
			}
			else{
				String simpleReadVarID = Variable.truncateSimpleID(readVar.getAliasVarID());
				String simpleVarID = Variable.truncateSimpleID(parent.getVarID());
				if(simpleReadVarID.equals(simpleVarID)){
					return readVar;
				}
			}
		}
		
		return null;
	}

	private List<VarValue> findSynonymousVarList(TraceNode thisStep, TraceNode thatStep, VarValue thisVar,
			boolean isOnBeforeTrace, PairList pairList, DiffMatcher matcher) {
		List<VarValue> readVariables = thatStep.getReadVariables();
		List<VarValue> synonymousList = new ArrayList<>();
		for(VarValue readVar: readVariables) {
			if(readVar.getVariable() instanceof ArrayElementVar && thisVar.getVariable() instanceof ArrayElementVar){
				
				String thisIndex = ((ArrayElementVar)thisVar.getVariable()).getIndex();
				String thatIndex = ((ArrayElementVar)readVar.getVariable()).getIndex();
				
				if(thisIndex!=null && thatIndex!=null && thisIndex.equals(thatIndex)){
					ReferenceValue thisParent = (ReferenceValue)thisVar.getParents().get(0);
					ReferenceValue thatParent = (ReferenceValue)readVar.getParents().get(0);
					
					VarValue thisReadParent = findReadParentVariable(thisParent, thisStep);
					VarValue thatReadParent = findReadParentVariable(thatParent, thatStep);
					System.currentTimeMillis();
					if(thisReadParent!=null && thatReadParent!=null){
						if(thisReadParent.getVarName().equals(thatReadParent.getVarName())){
							synonymousList.add(readVar);
						}
					}
					else{
						String thisParentID = Variable.truncateSimpleID(thisParent.getVarID());
						String thatParentID = Variable.truncateSimpleID(thatParent.getVarID());
						TraceNode thisDom = thisStep.getTrace().findLatestNodeDefiningVariable(
								thisParentID, thisStep.getOrder());
						TraceNode thatDom = thatStep.getTrace().findLatestNodeDefiningVariable(
								thatParentID, thatStep.getOrder());
						
						boolean isReferenceValueMatch = pairList.isPair(thisDom, thatDom, isOnBeforeTrace);
						if(isReferenceValueMatch){
							synonymousList.add(readVar);
						}
					}
				}
				
			}
			else{
				if(readVar.getVariable() instanceof VirtualVar && thisVar.getVariable() instanceof VirtualVar){
					String virName1 = readVar.getVarName();
					String virName2 = thisVar.getVarName();
					
					String simpleName1 = virName1.substring(virName1.lastIndexOf("#"), virName1.length());
					String simpleName2 = virName2.substring(virName2.lastIndexOf("#"), virName2.length());
					
					if(simpleName1.equals(simpleName2)){
						synonymousList.add(readVar);
					}
				}
				else if(readVar.getVarName().equals(thisVar.getVarName())) {
					synonymousList.add(readVar);
				}
			}
		}
		return synonymousList;
	}

	private boolean checkReturnVariable(TraceNode thisStep, TraceNode thatStep) {
		boolean isThisStepContainVirtual = false;
		boolean isThatStepContainVirtual = false;
		for(VarValue readVar: thisStep.getReadVariables()){
			if(readVar instanceof VirtualValue){
				isThisStepContainVirtual = true;
			}
		}
		
		for(VarValue readVar: thatStep.getReadVariables()){
			if(readVar instanceof VirtualValue){
				isThatStepContainVirtual = true;
			}
		}
		
		return isThisStepContainVirtual&&isThatStepContainVirtual;
	}

	public Trace getBuggyTrace() {
		return buggyTrace;
	}

	public void setBuggyTrace(Trace buggyTrace) {
		this.buggyTrace = buggyTrace;
	}

	public Trace getCorrectTrace() {
		return correctTrace;
	}

	public void setCorrectTrace(Trace correctTrace) {
		this.correctTrace = correctTrace;
	}
}
