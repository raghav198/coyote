from itertools import cycle
from coyote import *
from coyote.coyote_ast import Atom, Instr
from coyote.codegen import Schedule, codegen
from coyote.vectorize_circuit import CodeObject
import pickle 
import sys
from itertools import zip_longest
from itertools import chain



class Interleave:
    def __init__(self, inner0, inner1, number_sched):
        # self.sched_inner0_instr = inner0[0]         
        # self.sched_inner1_instr = inner1[0]
        # self.sched_inner2_instr = inner2[0]
        self.inner = [inner0, inner1]
        self.list_instr_len = [len(inner0[0]), len(inner1[0])]


        self.expansion_size = number_sched

        self.sched_inner0 = Schedule(inner0[1].lanes, inner0[1].alignment, inner0[0])         # The inner1 schedule
        self.sched_inner1 = Schedule(inner1[1].lanes, inner1[1].alignment, inner1[0])         # The inner2 schedule
        for i in  self.sched_inner0 :
            print(i)
        for i in  self.sched_inner1:
            print(i)

        # self.sched_inner2 = Schedule(inner2[1].lanes, inner2[1].alignment, self.sched_inner2_instr)         # The inner2 schedule
        self.inner_sched = [self.sched_inner0, self.sched_inner1]

        # self.sched_outer = Schedule(outer[1].lanes, outer[1].alignment, outer[0])         # The outer schedule
        self.instr_interleave = []
        self.lanes_inner0 = inner0[1].lanes
        self.lanes_inner1 = inner1[1].lanes
        # self.lanes_inner2 = inner2[1].lanes
        self.lanes_interleave = []
        self.operand_seq = []
        # print( len(self.sched_inner0.lanes),  len(self.sched_inner1.lanes))

        self.alignment_interleave = []
        self.aligned_op = []
        self.aligned_mapping = []
        self.interleave()



    def interleave(self):
            sum_instr_len = 0
            for itr, instr_len in enumerate(self.list_instr_len):
                instructions =  self.inner[itr][0]
                if (itr != 0):
                    for instr in instructions:
                        dest_reg =  sum_instr_len  + instr.dest.val 
                        if isinstance(instr.lhs, Atom) and isinstance(instr.lhs.val, int):
                            lhs_reg = int(instr.lhs.val) +  sum_instr_len
                            rhs_reg = int(instr.rhs.val) +  sum_instr_len
                            op_instr = instr.op
                            self.instr_interleave.append(Instr(dest_reg, Atom(lhs_reg), Atom(rhs_reg), op_instr))
                        else:
                            self.instr_interleave.append(Instr(dest_reg, Atom(instr.lhs.val), Atom(instr.rhs.val), "~"))
                    sum_instr_len += instr_len

                else:
                    self.instr_interleave = instructions
                    sum_instr_len += instr_len


            for i in range(self.expansion_size):
                for l in self.inner_sched[i].lanes:
                    self.lanes_interleave.append(self.expansion_size * l + i)
            self.operand_sequence()
            aligner = SequenceAligner()
            self.aligned_op = aligner.align_sequences(self.operand_seq)

            self.aligned_mapping = aligner.alignment_mapping(self.operand_seq, self.aligned_op)
            # print(self.aligned_mapping)
            for sched, map in zip(self.inner_sched, self.aligned_mapping):
                self.alignment_interleave.append(self.alignment(map, sched.steps))
            self.alignment_interleave = list(chain.from_iterable(self.alignment_interleave))


    def operand_sequence(self):
        for sched in self.inner_sched:
            sched_op= []
            for step in sched.steps:
                sched_op.append(sched.instructions[step[0]].op)
            self.operand_seq.append(sched_op)
        return 

    def alignment(self, format, initial_map):
        result = [None] * sum(len(sublist) for sublist in initial_map)
        for format_value, positions in zip(format, initial_map):
            for position in positions:
                result[position] = format_value
        return result

class SequenceAligner:
    def needleman_wunsch(self, seq1, seq2, match_score=1, mismatch_score=0, gap_penalty=-1):
        n, m = len(seq1), len(seq2)
        # create the score matrix
        score = [[0 for _ in range(m+1)] for _ in range(n+1)]
        # fill out the first row and column of the matrix
        for i in range(1, n+1):
            score[i][0] = i * gap_penalty
        for j in range(1, m+1):
            score[0][j] = j * gap_penalty
        # fill out the rest of the matrix
        for i in range(1, n+1):
            for j in range(1, m+1):
                if seq1[i-1] == seq2[j-1]:
                    match_mismatch = score[i-1][j-1] + match_score
                else:
                    match_mismatch = score[i-1][j-1] + mismatch_score
                insert = score[i][j-1] + gap_penalty
                delete = score[i-1][j] + gap_penalty
                score[i][j] = max(match_mismatch, insert, delete)
        # traceback
        align1, align2 = [], []
        i, j = n, m
        while i > 0 and j > 0:
            score_current = score[i][j]
            score_diagonal = score[i-1][j-1]
            score_up = score[i][j-1]
            score_left = score[i-1][j]
            if seq1[i-1] == seq2[j-1] or score_current == score_diagonal + mismatch_score:
                align1.append(seq1[i-1])
                align2.append(seq2[j-1])
                i -= 1
                j -= 1
            elif score_current == score_left + gap_penalty:
                align1.append(seq1[i-1])
                align2.append('-')
                i -= 1
            elif score_current == score_up + gap_penalty:
                align1.append('-')
                align2.append(seq2[j-1])
                j -= 1
        # finish tracing up to the top left cell
        while i > 0:
            align1.append(seq1[i-1])
            align2.append('-')
            i -= 1
        while j > 0:
            align1.append('-')
            align2.append(seq2[j-1])
            j -= 1
        # since we traversed the score matrix from the bottom right, we reverse the sequences
        align1.reverse()
        align2.reverse()
        return align1, align2
    
    def align_sequences(self, sequences):
        if len(sequences) < 2:
            return sequences
        
        # start with the alignment of the first two sequences
        aligned_seq1, aligned_seq2 = self.needleman_wunsch(sequences[0], sequences[1])
        alignments = [aligned_seq1, aligned_seq2]  # Store all alignments here
        
        # iteratively align each subsequent sequence with the alignments obtained so far
        for next_seq in sequences[2:]:
            new_alignments = []
            for aligned_seq in alignments:
                # align the next sequence with each of the aligned sequences so far
                aligned_next_seq, _ = self.needleman_wunsch(aligned_seq, next_seq)
                new_alignments.append(aligned_next_seq)
            
            # add the newly aligned sequence itself (aligned against the last of the current alignments)
            _, aligned_against_last = self.needleman_wunsch(alignments[-1], next_seq)
            new_alignments.append(aligned_against_last)
            
            alignments = new_alignments  # update alignments
        
        # since alignments are strings, convert them back to lists
        return alignments

    def alignment_mapping(self, original_sequences, aligned_sequences):
    
        mappings = []

        for orig, aligned in zip(original_sequences, aligned_sequences):
            orig_positions = list(range(len(orig)))  # Original positions [0, 1, 2, ...]
            mapped_positions = [-1] * len(orig)  # Initialize mapping with -1

            ai = 0  # index in the aligned sequence
            for oi in orig_positions:
                while ai < len(aligned):
                    if aligned[ai] == orig[oi]:
                        mapped_positions[oi] = ai
                        ai += 1
                        break
                    ai += 1

            mappings.append(mapped_positions)

        return mappings

def main(inner_schedule, outer_schedule):
    # Open the file to read the schedule
    with open(inner_schedule, "rb") as file:
        inner = pickle.load(file)  # inner schedule
    with open(inner_schedule, "rb") as file:
        inner = pickle.load(file)  # inner schedule
    with open(outer_schedule, "rb") as file_1:
        outer = pickle.load(file_1)  # outer schedule

    # Initialize  Interleave class
    Interleaved = Interleave(inner, outer, 2)

    # do interleaveing
    Interleaved_schedule = Schedule(Interleaved.lanes_interleave, Interleaved.alignment_interleave, Interleaved.instr_interleave)

    # print interleaved schedule
    # print(Atom)
    print('\n'.join(map(str, Interleaved.instr_interleave)))
    print('\n')
    codegen(Interleaved_schedule)
 
  


if __name__ == "__main__":
    # Check if the correct number of arguments 
    if len(sys.argv) != 3:
        print("Usage: script_name.py arg1 arg2")
        sys.exit(1)

    #  sys.argv[1] and sys.argv[2] are the inner schedule and outer schedule 
    arg1 = sys.argv[1]  # inner schedule
    arg2 = sys.argv[2]  # outer schedule


    main(arg1, arg2)