
# Execution model in Lean for (oracle) programs

- Non-oracle program semantics: $state \to distr(state)$.
- Non-oracle program language:
	- Individual operations to build semantics (no syntax formalization needed)
	- If, while (lfp?), bounded-for-loop (?), seq, assign, sample
- Oracle program semantics:
	- Approach 1 (simple):
		- Oracle program semantics are described by $A :: state \times oracleoutput \to distr(state \times oracleinput \times amIDoneBool)$
		- Oracle semantics by $O:oraclestate \times oracleinput \to distr(oraclestate \times oracleoutput)$
		- Interpretation of "A with O": run A, run O (with input from A), run A (with output from O), etc. etc. till A says stop.
		- Maybe: only need fixed query number oracle programs?
	- Approach 2 (powerful):
		- Programming language that has oracle calls like in EasyCrypt
		- Might not be needed for our adversary specs.
		- Possible nice to have (later):
			- Theorem that "appraoch 2" program can always be rewritten as "approach 1" program


# How to do pRHL?

Predicates are: $states\times states \to bool$.

How to syntax? $state :: (x:Var) \to Type(x)$.

Example predicate: Easycrypt `x{1} = x{2}`. In Lean (without syntax extensions): $\lambda(m1,m2). x(m1) = x(m2)$

pRHL definition: "prhl : pred -> sem -> sem -> pred -> bool"  (sem = non-oracle semantics, pred = predicate).

"prhl A c d B" means: $\forall m_1,m_2\text{ with }A(m1,m2). \exists \mu. map\ fst\ \mu = c(m1) \land map\ snd\ \mu = d(m2) \land satisfy(\mu,B)$
where:
$\mu :: distr(state \times state)$
$satisfy(\mu,B) := (\forall x. \mu(x)\neq 0 \implies B(x)) := Pr_\mu[\lnot B] = 0$.
$map\ f\ \mu := \text{applying function to distrib} := (\lambda x. \sum_{y\in f^{-1}(x)} \mu(y))$ (probably existing)

## Example: prhl {} c d {x1=x2} ==> Pr[x:c] = Pr[x:d]

Exists $\mu$ with properties from prhl-def (fix that)
w := weight \mu

lemma:
if nu satisties left=right: map(snd,\nu) = map(fst, %(x,y). (x,x), \nu) = map(%(x,y). x, \nu) = map(fst,\nu), thus map(snd,\nu)=map(fst,nu)

satisfy(\mu,x1=x2) ==> map((%(st1,st2). x(st1)=x(st2), \mu) is true
... ==> map(%(x1,x2). x1=x2, %(st1,st2). (x(st1),x(st2)), \mu) is true
... ==> (lemma)  map(fst, %(st1,st2). (x(st1),x(st2)), \mu) = map(snd, %(st1,st2). (x(st1),x(st2)), \mu) is true
... ==> map(x, fst, \mu) = map(x, snd, \mu)
... ==> map(x, c(m1)) = map(x, d(m2))
... ==> Pr[x:c] = Pr[x:d]



# Big steps

- Do background research
	- What's there for crypto in Lean
	- What game language?
	- Any Hoare logics? Other reasoning tools (especially for single protocols)
	- Any relational Hoare logic?
	- ArkLib? VCVio
- Formalize language, semantics, oracle-call semantics, pRHL def, etc.
- Show any needed pRHL theorems/tactics
- Define RO. (E.g., as lazy sampled, or as eager sampled, or both)
	- Show lazy/eager equivalence, if needed
- Formalize the relevant crypto definitions
	- Syntactic definitions: What is a PIOP, what is an interactive protocol, what is a ROM-NIZK, what is a PCS (poly comm. scheme)?
	- Security definitions:
		- PIOP: Completeness, computational soundness (for "trees")
		- Interactive proof: Completeness, computational soundness (for "trees")
		- Those two might be instances of same thing
		- PCS properties
		- Noninteractive proof in ROM: Completeness, computational soundness
- Formalize the constructions:
	- The Plonk PIOP
	- The PCS
	- The transformation PIOP + PCS -> IP
	- Fiat-Shamir of IP
	- (Summarizing: Plonk := all these together)
- Formalize the crypto results
	- Plonk PIOP: complete, computationally sound
	- PRIO + PCS: complete, computationally sound
	- Fiat-Shamir: complete, computationally sound
- 


## Random stuff

Want: RO $D\to R$.

OracleSpec with:
- $\iota := \mathbb N + D$
- Mapping $inl\ n$ to $\{0...n\}$
- Mapping $inr\ x$ to $R$

Interpretation:
- Program queries $inl\ n$: Return uniform element of $\{0...n\}$
- Program queries $inr\ x$: Return $RO(x)$.
- 

Because $x \leftarrow^\$ [n]$ is syntactic sugar for $x\leftarrow query(inl\ n)$.

OracleSpec for distribution sampling:
- $\iota$ is: `sigma x : T, distr(T)`