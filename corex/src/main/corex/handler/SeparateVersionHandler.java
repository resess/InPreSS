package corex.handler;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.io.PrintWriter;
import java.io.UnsupportedEncodingException;
import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.TimeUnit;

import org.apache.bcel.Repository;
import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;

import corex.projConfig;
import corex.empiricalstudy.DeadEndCSVWriter;
import corex.empiricalstudy.DeadEndRecord;
import corex.empiricalstudy.Defects4jProjectConfig;
import corex.empiricalstudy.EmpiricalTrial;
import corex.empiricalstudy.TrialGenerator;
import corex.empiricalstudy.TrialRecorder;
import corex.empiricalstudy.training.DED;
import corex.empiricalstudy.training.DeadEndData;
import corex.preference.CorexPreference;
import microbat.Activator;
import microbat.model.trace.Trace;


public class SeparateVersionHandler extends AbstractHandler{

	TrialGenerator generator0 = new TrialGenerator();
	
	//////////////////////////////////////////////////////////////////
	//////////////////////////////////////////////////////////////////
	//////////////////////////////////////////////////////////////////
	//////////////////////////////////////////////////////////////////
	//////////////////////////////////////////////////////////////////
	//////////////////////////////////////////////////////////////////
	public Object execute(ExecutionEvent event) throws ExecutionException {
		Job job = new Job("Running the project") {
			@Override
			protected IStatus run(IProgressMonitor monitor) {

				String basePath = Activator.getDefault().getPreferenceStore().getString(CorexPreference.REPO_PATH);
				String projectName = Activator.getDefault().getPreferenceStore().getString(CorexPreference.PROJECT_NAME);
				String bugID = Activator.getDefault().getPreferenceStore().getString(CorexPreference.BUG_ID);
				String proPath = PathConfiguration.getBugPath(projectName, bugID);
				String buggyPath = PathConfiguration.getBuggyPath(projectName, bugID);
				String fixPath = PathConfiguration.getCorrectPath(projectName, bugID);
				String testcase = Activator.getDefault().getPreferenceStore().getString(CorexPreference.TEST_CASE);
				String tool2Run = Activator.getDefault().getPreferenceStore().getString(CorexPreference.TOOL_2_RUN);
				
				
				System.out.println("working on the " + bugID + "the bug of " + projectName + " project.");
				
				boolean debug = false;    
				
				
				String EreasOrSlicer = "E";
				
				projConfig config;
				try {
					config = projConfig.getConfig(basePath, projectName, Integer.valueOf(bugID), EreasOrSlicer);
					List<String> includedClassNames = new ArrayList<>();
					List<String> excludedClassNames = new ArrayList<>();			
					generator0.generateTrials(basePath, projectName, bugID, proPath, buggyPath, fixPath, 
							true, true, true, 3, true, true, config, testcase, includedClassNames,excludedClassNames, config.configFile,debug,tool2Run);
				} catch (NumberFormatException | IOException | InterruptedException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
							
				return Status.OK_STATUS;
			}
			
			private void setTestCase(DED datas, String tc) {
				if(datas.getTrueData()!=null){
					datas.getTrueData().testcase = tc;					
				}
				for(DeadEndData data: datas.getFalseDatas()){
					data.testcase = tc;
				}
			}
		};
		
		job.schedule();
		
		return null;
	}
	
	

}
