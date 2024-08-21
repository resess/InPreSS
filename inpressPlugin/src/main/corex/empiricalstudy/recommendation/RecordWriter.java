/*
 * Copyright (C) 2013 by SUTD (Singapore)
 * All rights reserved.
 *
 * 	Author: SUTD
 *  Version:  $Revision: 1 $
 */

package corex.empiricalstudy.recommendation;

import java.io.OutputStream;
import java.io.PrintWriter;

import corex.empiricalstudy.training.DeadEndData;
import sav.strategies.vm.interprocess.TcpInputWriter;

/**
 * @author LLT
 *
 */
public class RecordWriter extends TcpInputWriter {
	private DeadEndData record;
	private PrintWriter pw;
	
	public RecordWriter() {
		waiting();
	}
	
	public void sendData(DeadEndData input) {
		if (isClosed()) {
			throw new IllegalStateException("InputWriter is closed!");
		}
		this.record = input;
		ready();
	}
	
	@Override
	protected void writeData() {
		String plainText = record.getPlainText("-1", "-1");
		pw.println(plainText);
		record = null;
	}
	
	public void setOutputStream(OutputStream outputStream) {
		this.pw = new PrintWriter(outputStream, true);
	}

	@Override
	public void close() {
		super.close();
		if (pw != null) {
			pw.close();
		}
	}
	
}
