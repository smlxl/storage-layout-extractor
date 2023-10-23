# Extending the Extractor

The primary extension point for this library comes in the form of improving the type inference
process. This process is made up of three major parts, two of which serve as extension points:

1. **Lifting (Extension Point):** This process takes the low-level symbolic values and adds
   higher-level constructs to them. These constructs are things that can be useful in multiple
   places, such as a dynamic array access. Lifting passes _may_ depend on the results of previous
   lifting passes. See [below](#writing-new-lifting-passes) for details on how to write new lifting
   passes.
2. **Inference (Extension Point):** Inference rules take the structure of the symbolic values after
   they have been modified by the lifting passes, and destructures them to create equations (see
   [below](#type-language)). Inferences _must not_ depend on the results of previous inference
   rules. See [below](#writing-new-inference-rules) for details on how to write new inference rules.
3. **Unification:** The unification process is where the results of the inference rules get
   combined. It is _not_ intended to be an extension point, but if the type language ever changes it
   will need to be modified.

## Type Language

During the inference process, every expression in the program has a _type variable_ associated with
it. This type variable can then have various _typing expressions_ associated with it. It is these
expressions that make up the inferences about a given type variable, and hence a given expression.

The type language in this library is kept _purposefully simple_, with only a few constructors and
the minimum number of composite types. These are as follows, and can be found at
their [definition](../src/tc/expression.rs):

- `Any`: This tells us nothing about the type, and exists as an "identity element" for the language
  of type expressions.
- `Equal`: This expression states that the type variable whose inference list it appears in _has the
  same type_ as the type variable (`id`) it is equal to.
- `Word`: This expression states that the type variable whose inference list it appears in is used
  as an EVM word with the specified properties (`width`, `signed`ness, and `usage`). The `usage`
  allows specifying more concrete uses of the word (e.g. as an `address`).
- `FixedArray`: This expression says that the type variable whose inference list it appears in is
  used as a fixed-length array on the EVM.
- `Mapping`: This expression says that the type variable whose inference list it appears in is used
  as a mapping on the EVM.
- `DynamicArray`: This expression says that the type variable whose inference list it appears in is
  used as a dynamically-sized array on the EVM.
- `Conflict`: It is possible that the extractor finds inferences that cannot be resolved. In that
  case, a conflict is produced. This is not an element of the language that should be created
  manually.

The type constructors (`FixedArray`, `Mapping`, and `DynamicArray`) are types that take _other
types_, in the form of type variables in their construction. That is to say that they are a type
that contains some other type by means of referencing other type variables. It is these type
variables that describe the contained type.

During inference, one or more expressions in this type language (called equations) are written into
the typing state.

## Writing New Inference Rules

Writing a new inference rule is a four-step process:

1. **Find a Pattern:** Inference rules are all based on patterns in the program values that _mean_
   something in terms of the value's type. The [manual inspection](../tests/manual_inspection.rs)
   test is a useful way to discover these patterns. Simply feed it a compiled contract that you are
   interested in, and set `should_print = true`. It will then print out all the keys and values that
   are written to the storage during execution.
2. **Describe the Equations:** The equations are what actually make an inference rule _work_, so
   carefully specifying these makes it possible to concretely establish what the pattern can tell us
   about the program's types.
3. **Implement the Rule:** Inference rules can often be quite simple to implement, as all that needs
   to be done is to match on the specified pattern, and then create the specific equations. The
   [existing rules](../src/tc/rule) are good documentation of how to do this.
4. **Test the Rule:** It is usually a good idea to write both unit tests (at the bottom of the file)
   and integration tests for the rules. See [the simple contract test](../tests/simple_contract.rs)
   for an example of how to write an integration test; all that needs to be done is create a
   contract that tests the property you want, compile it, and then assert properties on the result.

Care should be taken to make sure that the new inference rule does not conflict with existing rules.
If it does, this usually means that one of the rules is imprecise or incorrect, but in rare cases
the unifier may need to be changed.

### The Structure of Inference Rules

In order to make it possible to both precisely and concisely describe inference rules, there is a
little format we have for doing so. It is as follows:

```text
expression(of(multiple), parts) // An expression in the symbolic value representation
    a       b     c        d    // An assignment of type variables to each expression node
    
equating
- `a = b`                       // one or more equations
```

Let's work through an example inference rule for ascribing types based on dynamic arrays in storage,
as can be seen [here](../src/tc/rule/dynamic_array_write.rs).

First we start by writing out the pattern that we are trying to recognise. This tries to match the
output representation of the symbolic values as much as possible to make it easier to map between
the two mentally.

```text
s_store(storage_slot(dynamic_array<storage_slot(base_slot)>[index]), value)
```

Once this is done, the next step is to assign a type variable to _every single node_ in the
expression. Note that not all of these may end up used in the subsequent equations.

```text
s_store(storage_slot(dynamic_array<storage_slot(base_slot)>[index]), value)
   a          b            c             d          e         f        g
```

Here, it is clear that the entire expression `s_store(...)` has type variable `a`, while the storage
slot for the dynamic array `storage_slot(base_slot)` has type variable `d`.

Now it becomes possible to write the equations that we can glean from this pattern, all in terms of
the [type language](#type-language) discussed previously.

```text
s_store(storage_slot(dynamic_array<storage_slot(base_slot)>[index]), value)
   a          b            c             d          e         f        g
   
equating
- `d = dynamic_array<b>`
- `f = word(width = unknown, usage = UnsignedWord)`
- `b = g`
```

From here, it becomes simple to build and test an implementation of this rule as
seen [here](../src/tc/rule/dynamic_array_write.rs) in the codebase. It has both unit tests in
that file, and is integration tested in the test [here](../tests/simple_contract.rs).

## Writing New Lifting Passes

Where inference rules provide the means to say things about the types of values involved in a
program, lifting passes allow those values themselves to be manipulated. At first, this may seem a
little counter-intuitive, but there are common structures (e.g. mapping accesses) that we want to
treat as higher level concepts during inference, rather than as the low-level building blocks of
which they are made up.

The process is as follows:

1. **Find a Pattern:** All high-level operations are made up of a set of lower-level ones, so
   working out that pattern is the crucial first step.
2. **Create the Higher-Level Construct:** Unlike for inference rules, lifting passes require
   modifying the symbolic value representation to represent the new structure. Carefully consider
   what data to represent and what is unnecessary to keep.
3. **Implement the Pass:** Lifting passes are a bit more complex to implement as they require
   careful data transformation. Look at the [existing ones](../src/tc/lift) to get an idea of
   how to do this.
4. **Test the Pass:** It is usually a good idea to write both unit tests (at the bottom of the file)
   and integration tests for the rules. See [the simple contract test](../tests/simple_contract.rs)
   for an example of how to write an integration test; all that needs to be done is create a
   contract that tests the property you want, compile it, and then assert properties on the result.

### The Structure of Lifting Passes

Much like for inference rules, there is a little format that exists to concisely and comprehensively
describe lifting passes.

```text
expression(with(low, level), parts)

becomes

higher_level(expression, parts)
```

Let's work through an example lifting pass for finding accesses to mappings in storage as is
implemented [here](../src/tc/lift/mapping_index.rs).

First we start by writing out the low-level pattern that we are trying to represent at a
higher-level, using variable names to describe the arguments where their structure is irrelevant to
the lifting pass.

```text
sha3(concat(key, slot_ix))
```

From here, we use our newly-created higher-level construct to re-write it.

```text
sha3(concat(key, slot_ix))

becomes

mapping_ix<slot_ix>[key]
```

Now all that remains is to implement and test it, as can be seen in the
codebase [here](../src/tc/lift/mapping_index.rs).
