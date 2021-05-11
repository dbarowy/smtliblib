# smtliblib

This library is an SMTLIBv2 parser and AST. It is useful in two scenarios:

1. You need to parse SMTLIBv2 formulae into an AST.
2. You need to programmatically construct SMTLIBv2 formulae using AST node constructors, optionally outputting them as SMTLIBv2 text.

Note that this library is not yet complete. See [Contributing](#Contributing) below.

## Getting it

This library is available in NPM.

```
$ npm i smtliblib
```

`smtliblib` depends on the [parsecco](https://github.com/williams-cs/parsecco) parser library as well as [Typescript](https://www.typescriptlang.org/).

## Using it

The easiest way to use `smtliblib` is to use the top-level parsing function in the `SMT` namespace. The following example

```
import { SMT } from "smtliblib";

const text = "(define-fun plus ((a Int) (b Int)) Int (+ a b))";
const output = SMT.parse(text);
console.out(JSON.stringify(output));
```

will produce an AST that looks something like:

```
[
   {
      "name":"plus",
      "parameterList":[
         {
            "name":"a",
            "sort":{
               "value":0
            }
         },
         {
            "name":"b",
            "sort":{
               "value":0
            }
         }
      ],
      "returnSort":{
         "value":0
      },
      "impl":{
         "terms":[
            {
               "name":"a"
            },
            {
               "name":"b"
            }
         ]
      }
   }
]
```

## Serialization / Deserialization

To make sending SMTLIB ASTs over the wire easy, all AST nodes in this library know how to serialize themselves to and deserialize themselves from JSON. This is convenient because one can use `smtliblib` on both sides of a connection and have real Typescript types.

To use, refer to the `SMT.serialize` and `SMT.deserialize` helper functions.

Note that if you use this feature to send data via, e.g., a REST interface, you may still need to use Javascript's [`JSON.parse`](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/JSON/parse) and [`JSON.stringify`](https://www.w3schools.com/js/js_json_stringify.asp) functions.

For example, parsing an expression, serializing and then stringifying it:

```
const input = "(define-fun plus ((a Int) (b Int)) Int (+ a b))";
const output = SMT.parse(input);
const json = SMT.serialize(output);
const jsonStr = JSON.stringify(json);
```

and then later, parsing it and deserializing it:

```
const jsonObj = JSON.parse(jsonStr);
const output2 = SMT.deserialize(jsonObj);
```

where `output` is guaranteed to be exactly the same as `output2`.

## Contributing

This library is currently incomplete. I add features to it as I need them.

If you need a specific feature, feel free to [open an issue](https://github.com/dbarowy/smtliblib/issues). I am also happy to accept contributions via pull request.

## Acknowledgements

Development of this library was supported while working as a Visiting Researcher at Microsoft Research.
