import 'bootstrap';
import 'bootstrap/dist/css/bootstrap.min.css';

import { EditorView } from '@codemirror/next/view';
import { EditorState, languageData } from '@codemirror/next/state';
import { keymap } from '@codemirror/next/keymap';
import { standardKeymap } from '@codemirror/next/commands';
import { lineNumbers } from '@codemirror/next/gutter';
import { foldGutter } from '@codemirror/next/fold';
import { bracketMatching } from '@codemirror/next/matchbrackets';
import { closeBrackets } from '@codemirror/next/closebrackets';
import { defaultHighlighter, styleTags } from '@codemirror/next/highlight';
import { LezerSyntax, continuedIndent, indentNodeProp, foldNodeProp } from '@codemirror/next/syntax';
import { buildParser } from 'lezer-generator';
import grammar from 'raw-loader!./zord.grammar';

const parser = buildParser(grammar);
const zordSyntax = new LezerSyntax(parser.withProps(
  languageData.add({
    Program: {
      closeBrackets: { brackets: ['{', '(', '[', '<', '"'] },
      commentTokens: { line: "--", block: { open: "{-", close: "-}" } },
    }
  }),
  indentNodeProp.add({
    RecordType: continuedIndent(),
    Record: continuedIndent(),
  }),
  foldNodeProp.add({
    RecordType(tree) { return {from: tree.start + 1, to: tree.end - 1} },
    Record(tree) { return {from: tree.start + 1, to: tree.end - 1} },
  }),
  styleTags({
    'type extends def let letrec trait implements inherits': 'keyword definition',
    'if then else new open in forall': 'keyword',
    'override': 'modifier',
    'Int Double Bool String Top Bot Trait': 'keyword',
    Boolean: 'atom',
    Undefined: 'null',
    Unit: 'unit',
    TermName: 'variableName',
    TermNameDef: 'variableName definition',
    LabelDecl: 'propertyName definition',
    LineComment: 'lineComment',
    BlockComment: 'blockComment',
    Number: 'number',
    String: 'string',
    TypeOp: 'typeOperator',
    ArithOp: 'arithmeticOperator',
    LogicOp: 'logicOperator',
    CompareOp: 'compareOperator',
    MergeOp: 'operator',
    TraitArrow : 'punctuation definition',
    '( )': 'paren',
    '{ }': 'brace',
    '[ ]': 'squareBracket',
    '< >': 'angleBracket',
    '.': 'derefOperator',
    ', ;': 'separator',
  })
));

const state = EditorState.create({
  extensions: [
    keymap(standardKeymap),
    lineNumbers(),
    foldGutter(),
    bracketMatching(),
    closeBrackets,
    defaultHighlighter,
    zordSyntax.extension,
  ],
});
const view = new EditorView({ state });
document.getElementById('editor').appendChild(view.dom);

document.getElementById('run').onclick = () => {
  document.getElementById('output').append('Run button clicked. ');
};
