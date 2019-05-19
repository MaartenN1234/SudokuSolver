public class SudokuSolver {
	static private int dataModel [][] = new int [27][18];
	static private int metaData  [][] = new int [27][18];

	static private int zeroBucket[];
	static private int zeroBucketCount;
	static private int oneBucket[];
	static private int oneBucketCount;
	static private int twoBucket[];
	static private int twoBucketCount;
	static private int twoNPBucket[];
	static private int twoNPBucketCount;
	static private int restBucket[];
	static private int restBucketCount;

	/* ************************** *
	 *   Main iteration step      *
	 * ************************** */
	public static void main(String [] args){
		readExamplePuzzle();
		solve();
		display();
	}

	public static void solve(){
		calcAllMetaData();
		while(zeroBucketCount + oneBucketCount + twoBucketCount > 0)
			peelAndPropagate();
	}

	private static void peelAndPropagate(){
		
		if (zeroBucketCount != 0){
			int id = zeroBucket[--zeroBucketCount];
			propagateZero(id / 18, id % 18);
		} else if (oneBucketCount != 0){
			int id = oneBucket [--oneBucketCount];
			propagateOne(id / 18, id % 18);
		} else if (twoBucketCount != 0){
			int id =  twoBucket [--twoBucketCount];
			propagateTwo(id / 18, id % 18);
		} else if (twoNPBucketCount != 0){
			int id = twoNPBucket[--twoNPBucketCount];
			branchTwo(id / 18, id % 18);
		} else {
			int id = restBucket [--restBucketCount ];
			brachRest(id / 18, id % 18);
		}

	}

	private static void propagateZero (int i, int j){
		int number;
		int position;


		// 1. determine position and number
		if (j < 9){
			// position of a number is fixed
			number   = j;
			position = -dataModel[i][j];
		} else {
			// number in a position is fixed
			position = j - 9;
			number   = -dataModel[i][j];
		}

		System.out.println("p0 " +i+"," +j + ":" + dataModel[i][j]+"    pos"+position+": value"+(1+number));

		// 2. propagate in local matching
		for (int k=0; k<18; k++){
			if (k==number){
				// 2a.i  propagate positive to matching partner (or self)
				metaData [i][k] = 0;
				dataModel[i][k] = -position;
			} else if  (k==9+position){
				// 2a.ii propagate positive to matching partner (or self)
				metaData [i][k] = 0;
				dataModel[i][k] = -number;
			} else if (metaData [i][k] > 1) {
				// 2b    propagate negative to non-matching partner
				dataModel[i][k] &= nAndGate[k < 9 ? position : number];
				calcSingleMetaData(i,k);

				if (k<9){
					int nNAndGate = nAndGate[number];
					for(int l=0; l<9;l++)
						if (k!=l && k != position){
							int constrID1  = linkedConstraints[i][0][l]; // in 0 to 27
							int constrPos1 = linkedConstraints[i][1][l]; // in 0 to 9
							int constrID2  = linkedConstraints[i][2][l]; // in 0 to 27
							int constrPos2 = linkedConstraints[i][3][l]; // in 0 to 9
							if (dataModel[constrID1][constrPos1]>0){
								dataModel[constrID1][constrPos1] &= nNAndGate;
								calcSingleMetaData(constrID1,constrPos1);
								if (constrID1 ==24 && 1==number)
									System.out.println(dataModel[constrID1][constrPos1]+"("+metaData[constrID1][constrPos1]+") k:"+constrPos1+", pos"+position+": value"+(1+number));
							}
							if (dataModel[constrID2][constrPos2]>0){
								dataModel[constrID2][constrPos2] &= nNAndGate;
								calcSingleMetaData(constrID2,constrPos2);
								if (constrID2 ==24 && 1==number)
									System.out.println(dataModel[constrID2][constrPos2]+"("+metaData[constrID2][constrPos2]+") k:"+constrPos2+", pos"+position+": value"+(1+number));
							}
						}
				}
			}
		}

		// 3. propagate positive to the 2 sibling constraints
		int constrID1  = linkedConstraints[i][0][position]; // in 0 to 27
		int constrPos1 = linkedConstraints[i][1][position]; // in 0 to 9
		int constrID2  = linkedConstraints[i][2][position]; // in 0 to 27
		int constrPos2 = linkedConstraints[i][3][position]; // in 0 to 9
		if (metaData[constrID1][number] != 0){
			metaData[constrID1][number]      = 0;
			dataModel[constrID1][number]     = -constrPos1;
			zeroBucket[zeroBucketCount++]    = constrID1*18+number;
		}
		if (metaData[constrID2][number] != 0){
			metaData[constrID2][number]      = 0;
			dataModel[constrID2][number]     = -constrPos2;
			zeroBucket[zeroBucketCount++]    = constrID2*18+number;
		}
	}

	private static void propagateOne (int i, int j){
		if (metaData [i][j] == 1){
			metaData [i][j] = 0;
			System.out.println("p1 " + i+"," +j +":" + dataModel[i][j]);

			dataModel[i][j] = -whichBitFirst[dataModel[i][j]];
			propagateZero(i,j);
		}
	}
	private static void propagateTwo (int i, int j){
		if (metaData [i][j] == 2){
			// 1. propagate in local matching
			int dModValue = dataModel[i][j];

			if (j < 9){
				// Case 1a. two positions for a number possible
				for(int k=0; k<j; k++)
					if (dModValue == dataModel[i][k])
						for (int l=0; l<9; l++)
							if ( l!= k && l != j){
								dataModel[i][l] &= (511^dModValue);
								calcSingleMetaData(i,l);
							}
			} else {
				// Case 1b. two numbers for a position possible
				for(int k=9; k<j; k++)
					if (dModValue == dataModel[i][k])
						for (int l=9; l<18; l++)
							if (l != k && l != j){
								dataModel[i][l] &= (511^dModValue);
								calcSingleMetaData(i,l);
							}
			}

			// 2. propagate to sibling constraints
			if (j < 9){
				// Case 2a. two positions for a number possible
				int pos1   = whichBitFirst[dModValue];
				int pos2   = whichBitLast[dModValue];

				int constr1ID1  = linkedConstraints[i][0][pos1];
				int constr1ID2  = linkedConstraints[i][2][pos1];
				int constr2ID1  = linkedConstraints[i][0][pos2];
				int constr2ID2  = linkedConstraints[i][2][pos2];

				// Propagation possible when both positions relate to same constraint
				if (constr1ID1 == constr2ID1){
					int constrPos1  = 1 << linkedConstraints[i][1][pos1];
					int constrPos2  = 1 << linkedConstraints[i][1][pos2];
					metaData[constr1ID1][j] &= (constrPos1|constrPos2);
					calcSingleMetaData(constr1ID1, j);
				} else if (constr1ID1 == constr2ID2){
					int constrPos1  = 1 << linkedConstraints[i][1][pos1];
					int constrPos2  = 1 << linkedConstraints[i][3][pos2];
					metaData[constr1ID1][j] &= (constrPos1|constrPos2);
					calcSingleMetaData(constr1ID1, j);
				}

				if (constr1ID2 == constr2ID1){
					int constrPos1  = 1 << linkedConstraints[i][3][pos1];
					int constrPos2  = 1 << linkedConstraints[i][1][pos2];
					metaData[constr1ID2][j] &= (constrPos1|constrPos2);
					calcSingleMetaData(constr1ID2, j);
				} else if (constr1ID2 == constr2ID2){
					int constrPos1  = 1 << linkedConstraints[i][3][pos1];
					int constrPos2  = 1 << linkedConstraints[i][3][pos2];
					metaData[constr1ID2][j] &= (constrPos1|constrPos2);
					calcSingleMetaData(constr1ID2, j);
				}
			} else {
				// Case 2b. two numbers for a position possible --> propagate to siblings
				int position = j - 9;

				// propagate to the 2 sibling constraints
				int constrID1  =   linkedConstraints[i][0][position]; // in 0 to 27
				int constrPos1 = 9+linkedConstraints[i][1][position]; // in 0 to 9
				int constrID2  =   linkedConstraints[i][2][position]; // in 0 to 27
				int constrPos2 = 9+linkedConstraints[i][3][position]; // in 0 to 9

				metaData[constrID1][constrPos1] &= dModValue;
				calcSingleMetaData(constrID1, constrPos1);
				metaData[constrID2][constrPos2] &= dModValue;
				calcSingleMetaData(constrID2, constrPos2);
			}

			// 3. Push into propagated bucket
			twoNPBucket [twoNPBucketCount++]  = i*18+j;
		}
	}
	private static void branchTwo (int i, int j){
		if (metaData [i][j] == 2){
		}
	}
	private static void brachRest (int i, int j){
		if (metaData [i][j] > 2){
		}
	}

	/* ************************** *
	 *   Calculating meta data    *
	 * ************************** */
	public static void calcAllMetaData(){
		zeroBucket      = new int [486];
		zeroBucketCount = 0;
		oneBucket       = new int [486];
		oneBucketCount  = 0;
		twoBucket       = new int [486];
		twoBucketCount  = 0;
		twoNPBucket     = new int [486];
		twoNPBucketCount= 0;
		restBucket      = new int [486];
		restBucketCount = 0;

		for (int i=0; i< dataModel.length; i++)
			for (int j=0; j<dataModel[i].length; j++){
				metaData[i][j] = -99;
				calcSingleMetaData(i,j);
			}
	}
	// metaData[constraintID][row_colID] = nrOfBits(dataModel[constraintID][row_colID])
	private static void calcSingleMetaData(int i, int j){
		int in  = dataModel[i][j];
		int out = in < 0 ? 0 : nrOfBitsProxy[in];
		if (metaData[i][j] != out){
			switch(out){
			case 0:
				zeroBucket[zeroBucketCount++] = i*18+j;
				break;
			case 1:
				oneBucket [oneBucketCount++]  = i*18+j;
				break;
			case 2:
				twoBucket [twoBucketCount++]  = i*18+j;
				break;
			}
			metaData[i][j] = out;
		}
	}

	/* ************************** *
	 *   Debug info               *
	 * ************************** */
	static void display(){
		String s="";
		for (int i=0; i<9; i++){
			if (i==3 || i==6)
				s=s+"\n";
			s = s +"\n";
			for (int j=9; j<18; j++){
				if (j==12|| j==15)
					s=s+" ";
				s = s + (dataModel[i][j]<=0? 1-dataModel[i][j]:".");
			}
		}
		System.out.println(s);
	}


	/* ************************** *
	 *   Lookup arrays            *
	 * ************************** */
	static int nrOfBitsProxy[]         = new int[512];
	static int whichBitFirst[]         = new int[512];
	static int whichBitLast[]          = new int[512];
	static int nAndGate[]              = new int[9];
	static int linkedConstraints[][][] = new int[27][4][9];

	static {
		for(int i=0; i< 512; i++){
			int sum = 0;
			for (int k=0; k<9; k++)
				sum += (i >> k & 1);
			nrOfBitsProxy[i] = sum;
		}

		for(int i=0; i< 512; i++){
			whichBitFirst[i] = 0;
			whichBitLast[i]  = 0;
		}
		// Singles
		whichBitFirst[1]   = 1;		whichBitFirst[2]   = 2;		whichBitFirst[4]   = 3;		whichBitFirst[8]   = 4;		whichBitFirst[16]  = 5;		whichBitFirst[32]  = 6;		whichBitFirst[64]  = 7;		whichBitFirst[128] = 8;		whichBitFirst[256] = 9;
		// Doubles first bit
		whichBitFirst[3]   = 1;		whichBitFirst[5]   = 1;		whichBitFirst[9]   = 1;		whichBitFirst[17]  = 1;		whichBitFirst[33]  = 1;		whichBitFirst[65]  = 1;		whichBitFirst[129] = 1;		whichBitFirst[257] = 1;
		whichBitFirst[6]   = 2;		whichBitFirst[10]  = 2;		whichBitFirst[18]  = 2;		whichBitFirst[34]  = 2;		whichBitFirst[66]  = 2;		whichBitFirst[130] = 2;		whichBitFirst[258] = 2;
		whichBitFirst[12]  = 3;		whichBitFirst[20]  = 3;		whichBitFirst[36]  = 3;		whichBitFirst[68]  = 3;		whichBitFirst[132] = 3;		whichBitFirst[260] = 3;
		whichBitFirst[24]  = 4;		whichBitFirst[40]  = 4;		whichBitFirst[72]  = 4;		whichBitFirst[136] = 4;		whichBitFirst[264] = 4;		whichBitFirst[48]  = 5;		whichBitFirst[80]  = 5;		whichBitFirst[144] = 5;		whichBitFirst[272] = 5;
		whichBitFirst[96]  = 6;		whichBitFirst[160] = 6;		whichBitFirst[288] = 6;		whichBitFirst[192] = 7;		whichBitFirst[320] = 7;		whichBitFirst[384] = 8;
		// Doubles second bit
		whichBitLast[3]   = 2;		whichBitLast[5]   = 3;		whichBitLast[9]   = 4;		whichBitLast[17]  = 5;		whichBitLast[33]  = 6;		whichBitLast[65]  = 7;		whichBitLast[129] = 8;		whichBitLast[257] = 9;
		whichBitLast[6]   = 3;		whichBitLast[10]  = 4;		whichBitLast[18]  = 5;		whichBitLast[34]  = 6;		whichBitLast[66]  = 7;		whichBitLast[130] = 8;		whichBitLast[258] = 9;
		whichBitLast[12]  = 4;		whichBitLast[20]  = 5;		whichBitLast[36]  = 6;		whichBitLast[68]  = 7;		whichBitLast[132] = 8;		whichBitLast[260] = 9;
		whichBitLast[24]  = 5;		whichBitLast[40]  = 6;		whichBitLast[72]  = 7;		whichBitLast[136] = 8;		whichBitLast[264] = 9;		whichBitLast[48]  = 6;		whichBitLast[80]  = 7;		whichBitLast[144] = 8;		whichBitLast[272] = 9;
		whichBitLast[96]  = 7;		whichBitLast[160] = 8;		whichBitLast[288] = 9;		whichBitLast[192] = 8;		whichBitLast[320] = 9;		whichBitLast[384] = 9;
		for(int i=0; i< 512; i++){
			whichBitFirst[i]--;
			whichBitLast[i]--;
		}

		int k=1;
		for (int i=0; i<9; i++){
			nAndGate[i] = 511 ^ k;
			k *=2;
		}
		/*
         11 111 111
	    901 234 567

	0	012 012 012
	1	345 345 345
	2	678 678 678

	3	012 012 012
	4	345 345 345
	5	678 678 678

	6	012 012 012
	7	345 345 345
	8	678 678 678
		 */
		for(int i=0; i<9; i++)
			for(int j=0; j<9; j++){
				//Horizontal constraints to vertical
				linkedConstraints[i][0][j] = j+9;
				linkedConstraints[i][1][j] = i;
				//Vertical constraints to horizontal
				linkedConstraints[j+9][0][i] = i;
				linkedConstraints[j+9][1][i] = j;
				//Horizontal constraints to block
				int hBlockNo  = (j / 3) + 3 * (i / 3) + 18;
				int hBlockPos = (j % 3) + 3 * (i % 3);
				linkedConstraints[i][2][j]   = hBlockNo;
				linkedConstraints[i][3][j]   = hBlockPos;
				// Block to horizontal
				linkedConstraints[hBlockNo][0][hBlockPos]   = i;
				linkedConstraints[hBlockNo][1][hBlockPos]   = j;
				//Vertical constraints to block
				int vBlockNo  = (i / 3) + 3 * (j / 3) + 18;
				int vBlockPos = (i % 3) + 3 * (j % 3);
				linkedConstraints[i+9][2][j]   = vBlockNo;
				linkedConstraints[i+9][3][j]   = vBlockPos;
				// Block to horizontal
				linkedConstraints[vBlockNo][2][vBlockPos]   = i+9;
				linkedConstraints[vBlockNo][3][vBlockPos]   = j;
			}
	}

	/* ************************** *
	 *   example puzzle           *
	 * ************************** */
	static public void readExamplePuzzle(){
		dataModel = new int [27][18];
		// ..3  ..8  ...
		// .4.  59.  .2.
		// 1..  ...  35.

		// .7.  .5.  ..9
		// ...  8.4  ...
		// 2..  .6.  .4.

		// .97  ...  ..3
		// .5.  .37  .8.
		// ...  2..  5..
		for (int i=0; i<27; i++)
			for (int j=0; j<18; j++)
				dataModel[i][j] = 511;

		dataModel[0][9+2] = 1-3; dataModel[0][9+5] = 1-8;
		dataModel[1][9+1] = 1-4; dataModel[1][9+3] = 1-5;dataModel[1][9+4] = 1-9; dataModel[1][9+7] = 1-2;
		dataModel[2][9+0] = 1-1; dataModel[2][9+6] = 1-3;dataModel[2][9+7] = 1-5;

		dataModel[3][9+1] = 1-7; dataModel[3][9+4] = 1-5;dataModel[3][9+8] = 1-9;
		dataModel[4][9+3] = 1-8; dataModel[4][9+5] = 1-4;
		dataModel[5][9+0] = 1-2; dataModel[5][9+4] = 1-6;dataModel[5][9+7] = 1-4;

		dataModel[6][9+1] = 1-9; dataModel[6][9+2] = 1-7;dataModel[6][9+8] = 1-3;
		dataModel[7][9+1] = 1-5; dataModel[7][9+4] = 1-3;dataModel[7][9+5] = 1-7; dataModel[7][9+7] = 1-8;
		dataModel[8][9+3] = 1-2; dataModel[8][9+6] = 1-5;
	}
}
