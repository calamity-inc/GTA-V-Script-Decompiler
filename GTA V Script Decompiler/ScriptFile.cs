using System;
using System.Collections.Generic;
using System.Globalization;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.IO;
using System.IO.Compression;
using System.Threading;

namespace Decompiler
{
	public class ScriptFile
    {
        List<byte> CodeTable;
		public StringTable StringTable;
		public NativeTable NativeTable;
		public X64NativeTable X64NativeTable;
        private int offset = 0;
        public readonly bool ConsoleVer;
		public List<Function> Functions;
		public Dictionary<int, FunctionName> FunctionLoc;
		public static Hashes hashbank;
        private Stream file;
		public ScriptHeader Header;
        public string name;
        internal Vars_Info Statics;
        internal bool CheckNative = true;
		internal static NativeParamInfo npi;
		internal static x64BitNativeParamInfo X64npi = new x64BitNativeParamInfo();
        

     

        public Dictionary<string, Tuple<int, int>> Function_loc = new Dictionary<string, Tuple<int,int>>();
        
        public ScriptFile(Stream scriptStream, bool Console)
        {
            ConsoleVer = Console;
            file = scriptStream;
            Header = ScriptHeader.Generate(scriptStream, Console);
            StringTable = new StringTable(scriptStream, Header.StringTableOffsets, Header.StringBlocks, Header.StringsSize);
            if (Console)
                NativeTable = new NativeTable(scriptStream, Header.NativesOffset + Header.RSC7Offset, Header.NativesCount);
            else
                X64NativeTable = new X64NativeTable(scriptStream, Header.NativesOffset + Header.RSC7Offset, Header.NativesCount, Header.CodeLength);
            name = Header.ScriptName;
            CodeTable = new List<byte>();
            for (int i = 0; i < Header.CodeBlocks; i++)
            {
                int tablesize = ((i + 1) * 0x4000 >= Header.CodeLength) ? Header.CodeLength % 0x4000 : 0x4000;
                byte[] working = new byte[tablesize];
                scriptStream.Position = Header.CodeTableOffsets[i];
                scriptStream.Read(working, 0, tablesize);
                CodeTable.AddRange(working);
            }
            GetStaticInfo();
            Functions = new List<Function>();
            FunctionLoc = new Dictionary<int, FunctionName>();
            GetFunctions();
            foreach (Function func in Functions)
            {
                func.PreDecode();
            }
            Statics.checkvars();
            foreach (Function func in Functions)
            {
                func.Decode();
            }
        }


        public void Save(string filename)
        {
            Stream savefile = File.Create(filename);
            Save(savefile, true);
        }
        public void Save(Stream stream, bool close = false)
        {
            int i = 1;
            StreamWriter savestream = new StreamWriter(stream);
            if (Program.Declare_Variables)
            {
                if (Header.StaticsCount > 0)
                {
                    savestream.WriteLine("#region Local Var");
                    i++;
                    foreach (string s in Statics.GetDeclaration(ConsoleVer))
                    {
                        savestream.WriteLine("\t" + s);
                        i++;
                    }
                    savestream.WriteLine("#endregion");
                    savestream.WriteLine("");
                    i += 2;
                }
            }
            foreach (Function f in Functions)
            {
                string s = f.ToString();
                savestream.WriteLine(s);
                Function_loc.Add(f.Name, new Tuple<int,int>( i, f.Location));
                i += f.LineCount;
            }
            savestream.Flush();
            if (close)
                savestream.Close();
        }
        public void Close()
        {
            file.Close();
        }

        public string[] GetStringTable()
        {
            List<string> table = new List<string>();
            foreach (KeyValuePair<int, string> item in StringTable)
            {
                table.Add(item.Key.ToString() + ": " + item.Value);
            }
            return table.ToArray();
        }

        public string[] GetNativeTable()
        {
	        if (ConsoleVer)
		        return NativeTable.GetNativeTable();
	        else
		        return X64NativeTable.GetNativeTable();
        }
        public string[] GetNativeHeader()
        {
	        if (ConsoleVer)
		        return NativeTable.GetNativeHeader();
	        else
		        return X64NativeTable.GetNativeHeader();
        }

        public void GetFunctionCode()
        {
            for (int i = 0; i < Functions.Count - 1; i++)
            {
                int start = Functions[i].MaxLocation;
                int end = Functions[i + 1].Location;
                Functions[i].CodeBlock = CodeTable.GetRange(start, end - start);
            }
            Functions[Functions.Count - 1].CodeBlock = CodeTable.GetRange(Functions[Functions.Count - 1].MaxLocation, CodeTable.Count - Functions[Functions.Count - 1].MaxLocation);
            foreach (Function func in Functions)
            {
                if (func.CodeBlock[0] != 45 && func.CodeBlock[func.CodeBlock.Count - 3] != 46)
                    throw new Exception("Function has incorrect start/ends");
            }
        }
        void advpos(int pos)
        {
            offset += pos;
        }
        void AddFunction(int start1, int start2)
        {
            byte namelen = CodeTable[start1 + 4];
            string name = "";
            if (namelen > 0)
            {
                for (int i = 0; i < namelen; i++)
                {
                    name += (char)CodeTable[start1 + 5 + i];
                }
            }
            else if (start1 == 0)
            {
                name = "__EntryFunction__";
            }
            else name = "func_" + Functions.Count.ToString();
            int pcount = CodeTable[offset + 1];
            int tmp1 = CodeTable[offset + 2], tmp2 = CodeTable[offset + 3];
            int vcount = ((ConsoleVer)? (tmp1 << 0x8) | tmp2 : (tmp2 << 0x8) | tmp1) ;
            if (vcount < 0)
            {
                throw new Exception("Well this shouldnt have happened");
            }
            int temp = start1 + 5 + namelen;
            while ((Instruction)CodeTable[temp] != Instruction.Return)
            {
                switch ((Instruction)CodeTable[temp])
                {
                    case Instruction.iPushByte1: temp += 1; break;
                    case Instruction.iPushByte2: temp += 2; break;
                    case Instruction.iPushByte3: temp += 3; break;
                    case Instruction.iPushInt:
                    case Instruction.fPush: temp += 4; break;
                    case Instruction.Native: temp += 3; break;
                    case Instruction.Enter: throw new Exception("Return Expected");
                    case Instruction.Return: throw new Exception("Return Expected");
                    case Instruction.pArray1:
                    case Instruction.ArrayGet1:
                    case Instruction.ArraySet1:
                    case Instruction.pFrame1:
                    case Instruction.GetFrame1:
                    case Instruction.SetFrame1:
                    case Instruction.pStatic1:
                    case Instruction.StaticGet1:
                    case Instruction.StaticSet1:
                    case Instruction.Add1:
                    case Instruction.Mult1:
                    case Instruction.pStruct1:
                    case Instruction.GetStruct1:
                    case Instruction.SetStruct1: temp += 1; break;
                    case Instruction.iPushShort:
                    case Instruction.Add2:
                    case Instruction.Mult2:
                    case Instruction.pStruct2:
                    case Instruction.GetStruct2:
                    case Instruction.SetStruct2:
                    case Instruction.pArray2:
                    case Instruction.ArrayGet2:
                    case Instruction.ArraySet2:
                    case Instruction.pFrame2:
                    case Instruction.GetFrame2:
                    case Instruction.SetFrame2:
                    case Instruction.pStatic2:
                    case Instruction.StaticGet2:
                    case Instruction.StaticSet2:
                    case Instruction.pGlobal2:
                    case Instruction.GlobalGet2:
                    case Instruction.GlobalSet2:
                    case Instruction.Jump:
                    case Instruction.JumpFalse:
                    case Instruction.JumpNe:
                    case Instruction.JumpEq:
                    case Instruction.JumpLe:
                    case Instruction.JumpLt:
                    case Instruction.JumpGe:
                    case Instruction.JumpGt: temp += 2; break;
                    case Instruction.Call:
                    case Instruction.pGlobal3:
                    case Instruction.GlobalGet3:
                    case Instruction.GlobalSet3:
                    case Instruction.iPushI24: temp += 3; break;
                    case Instruction.Switch: temp += 1 + CodeTable[temp + 1] * 6; break;
                    case Instruction.StrCopy:
                    case Instruction.ItoS:
                    case Instruction.StrConCat:
                    case Instruction.StrConCatInt: temp += 1; break;
                }
                temp += 1;
            }
            int rcount = CodeTable[temp + 2];
            int Location = start2;
            if (start1 == start2)
            {
                Functions.Add(new Function(this, name, pcount, vcount, rcount, Location));
            }
            else
                Functions.Add(new Function(this, name, pcount, vcount, rcount, Location, start1));
        }
        void GetFunctions()
        {
            int returnpos = -3;
            while (offset < CodeTable.Count)
            {
                switch ((Instruction)CodeTable[offset])
                {
                    case Instruction.iPushByte1: advpos(1); break;
                    case Instruction.iPushByte2: advpos(2); break;
                    case Instruction.iPushByte3: advpos(3); break;
                    case Instruction.iPushInt:
                    case Instruction.fPush: advpos(4); break;
                    case Instruction.Native: advpos(3); break;
                    case Instruction.Enter: AddFunction(offset, returnpos + 3); ; advpos(CodeTable[offset + 4] + 4); break;
                    case Instruction.Return: returnpos = offset; advpos(2); break;
                    case Instruction.pArray1:
                    case Instruction.ArrayGet1:
                    case Instruction.ArraySet1:
                    case Instruction.pFrame1:
                    case Instruction.GetFrame1:
                    case Instruction.SetFrame1:
                    case Instruction.pStatic1:
                    case Instruction.StaticGet1:
                    case Instruction.StaticSet1:
                    case Instruction.Add1:
                    case Instruction.Mult1:
                    case Instruction.pStruct1:
                    case Instruction.GetStruct1:
                    case Instruction.SetStruct1: advpos(1); break;
                    case Instruction.iPushShort:
                    case Instruction.Add2:
                    case Instruction.Mult2:
                    case Instruction.pStruct2:
                    case Instruction.GetStruct2:
                    case Instruction.SetStruct2:
                    case Instruction.pArray2:
                    case Instruction.ArrayGet2:
                    case Instruction.ArraySet2:
                    case Instruction.pFrame2:
                    case Instruction.GetFrame2:
                    case Instruction.SetFrame2:
                    case Instruction.pStatic2:
                    case Instruction.StaticGet2:
                    case Instruction.StaticSet2:
                    case Instruction.pGlobal2:
                    case Instruction.GlobalGet2:
                    case Instruction.GlobalSet2:
                    case Instruction.Jump:
                    case Instruction.JumpFalse:
                    case Instruction.JumpNe:
                    case Instruction.JumpEq:
                    case Instruction.JumpLe:
                    case Instruction.JumpLt:
                    case Instruction.JumpGe:
                    case Instruction.JumpGt: advpos(2); break;
                    case Instruction.Call:
                    case Instruction.pGlobal3:
                    case Instruction.GlobalGet3:
                    case Instruction.GlobalSet3:
                    case Instruction.iPushI24: advpos(3); break;
                    case Instruction.Switch: advpos(1 + CodeTable[offset + 1] * 6); break;
                    case Instruction.StrCopy:
                    case Instruction.ItoS:
                    case Instruction.StrConCat:
                    case Instruction.StrConCatInt: advpos(1); break;
                }
                advpos(1);
            }
            offset = 0;
            GetFunctionCode();
        }
        private void GetStaticInfo()
        {
            Statics = new Vars_Info(Vars_Info.ListType.Statics);
			Statics.SetScriptParamCount(Header.ParameterCount);
            IO.Reader reader = new IO.Reader(file, ConsoleVer);
            reader.BaseStream.Position = Header.StaticsOffset + Header.RSC7Offset;
            for (int count = 0; count < Header.StaticsCount; count++)
            {
                if (ConsoleVer)
                    Statics.AddVar(reader.SReadInt32());
                else
                    Statics.AddVar(reader.ReadInt64());
            }
        }

    }
    
 


   

    


}
