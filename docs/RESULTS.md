# Results

The short form of the study "Proved is not finished". The paper has each number with its method and its
limits: https://puppetmaster.gg/labs/hard-proof/paper/ ([PDF](paper.pdf)).

## The idea in five sentences

A proof gate accepts a code change only when a checker accepts a machine-checked proof for each law
that a human owns. That forces "the code obeys the laws". It does not force "the laws say enough".
An adversary agent can prove what the laws leave open: it supplies two designs that pass each law and
one input on which they differ. That gap becomes one concrete question for the human, the answer
becomes a new law, and the loop stops when the checker accepts a proof that no gap is left.

## What the data says

Each number is in the paper, with the command that gives it.

| Result | Evidence |
| --- | --- |
| Agents find gaps and prove completeness with machine-checked certificates | 73 gap certificates and 66 completeness proofs in 144 adversary runs of the first study |
| A plain review finds most gaps for the same cost | 22 of 27 gaps at 48 decision points, with no proof |
| The proof duty finds a gap that review misses | One fault in a definition: 0 of 12 reviews, 3 of 3 proof runs |
| A review loop can stop early; a proof loop ends on a theorem | A review loop "until dry" ended on a false "complete" in 3 of 6 law sets |
| Durable sessions make later rounds cheap | A later round costs $0.06 to $0.31, a first visit $0.40 to $0.49 |
| A pointed agent review misses more than half of real bugs | The best of three review arms found 44 of 95 real bugs of two products |
| A full proof pipeline does not replace a review, and it finds different bugs | 31 of 95 for about 8 times the cost of the best review arm; 6 of the 40 bugs that three review arms missed |
| An audit ladder turns review findings into fixes | 211 findings gave 45 confirmed bugs; 51 fixes shipped in Puppetmaster 1.51.2 and Marionette 0.9.685, and 5 more corrections in 1.51.3 and 0.9.686 |
| A conflict between code and a law is most often a fault of the law | 73 live conflicts from the pipeline: 0 reachable bugs, 3 latent faults, 2 wrong documentation sentences, 57 laws that say more than the sentence |
| The release gate works on real releases | It fails on Puppetmaster 1.51.1 (7 open bugs) and passes on 1.51.2 (7 closed). Its first two release runs: 8 changed functions, no confirmed bug, 16.33 US dollars |
| A small decision rule gets a completeness proof in minutes | The swarm policy table of Marionette: 5 laws, 16 input cases, accepted by 6 kernels; its docstring alone left one input open |

The study also reports what did not work: one of its own "blind" tests was not blind, a fix step with
a test and a judge let 5 of 45 wrong fixes through, a runner fault ran six bugs of the pipeline test two times, and the runs took the test machine down one time.
