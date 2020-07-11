import 'bootstrap';
import 'bootstrap/dist/css/bootstrap.min.css';

import { EditorState, EditorView, basicSetup } from '@codemirror/next/basic-setup';
import { styleTags } from '@codemirror/next/highlight';
import { LezerSyntax, continuedIndent, indentNodeProp, foldNodeProp } from '@codemirror/next/syntax';
import { parser } from './zord';

import Zord from '../src/Zord.purs';

const zordSyntax = new LezerSyntax(parser.withProps(
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
), {
  languageData: {
    closeBrackets: { brackets: ['{', '(', '[', '<', '"'] },
    commentTokens: { line: "--", block: { open: "{-", close: "-}" } },
  }
});

const state = EditorState.create({
  extensions: [
    basicSetup,
    zordSyntax.extension,
  ],
});
const view = new EditorView({ state, parent: document.getElementById('editor') });

document.getElementById('run').onclick = () => {
  const output = document.getElementById('output');
  const error = document.getElementById('error');
  output.textContent = error.textContent = '';
  try {
    output.textContent = Zord.interpret(view.state.doc.toString())();
  } catch (err) {
    error.textContent = err;
  }
};
