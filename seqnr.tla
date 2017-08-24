\*
\* Copyright (c) 2017 Thales Austria GmbH
\*
\* Permission is hereby granted, free of charge, to any person obtaining a copy
\* of this software and associated documentation files (the "Software"), to deal
\* in the Software without restriction, including without limitation the rights
\* to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
\* copies of the Software, and to permit persons to whom the Software is
\* furnished to do so, subject to the following conditions:
\* 
\* The above copyright notice and this permission notice shall be included in all
\* copies or substantial portions of the Software.
\* 
\* THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
\* IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
\* FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
\* AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
\* LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
\* OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
\* SOFTWARE.
\*

-------------------------------- MODULE seqnr ---------------------------------

EXTENDS Integers, TLC

\******************************************************************************
\* Sequence Numbers

\* Highest sync. sequence number
CONSTANT MAX_SEQNR


            
\* increment sync sequence number, returns to 0 after reaching
\* MAX_SEQNR
inc_seqnr(nr) ==
    IF nr = MAX_SEQNR
        THEN 0
        ELSE nr + 1

\* compare sequence numbers that are arranged in a circle
\* returns:
\*  0           if nr1 == nr2
\*  pos. value  if nr1 was issued after nr2
\*  neg. value  if nr1 was issued before nr2
\*  undef (failing assertion)   if it the order cannot be determined
cmp_seqnr(nr1, nr2) ==
    LET
        numberOfSeqnr == MAX_SEQNR + 1
        
        diffMod == (nr1 - nr2) % numberOfSeqnr 
        isEven == numberOfSeqnr % 2 = 0
        half == numberOfSeqnr \div 2
    IN
    CASE
        \* nr1 later issued than nr2    
        diffMod < half ->
            diffMod
                []
                
        \* nr2 later issued than nr1
        \* -> substract diffMod from half to return negative value         
        diffMod > half ->
            diffMod - numberOfSeqnr
                []
                
        \* with uneven number of sequence numbers, when diffMod is half
        \* nr1 was issued later than nr2
        ~isEven /\ diffMod = half ->
            diffMod
                []
            
        \* cornercase with even number of sequence numbers and diffMod
        \* beeing half we can not determine which one was issued first
        \* -> uncomparable value
        isEven /\ diffMod = half ->
            Assert(FALSE, "cannot determine order of seqnrs")


===============================================================================

