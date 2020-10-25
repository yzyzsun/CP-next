import 'bootstrap';
import 'bootstrap/dist/css/bootstrap.min.css';

import { EditorState, EditorView, basicSetup } from '@codemirror/next/basic-setup';
import { ViewPlugin, keymap } from '@codemirror/next/view';
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
    RecordType(tree) { return { from: tree.start + 1, to: tree.end - 1 } },
    Record(tree) { return { from: tree.start + 1, to: tree.end - 1 } },
  }),
  styleTags({
    'type extends let letrec trait implements inherits': 'keyword definition',
    'if then else new open in toString forall Int Double Bool String Top Bot Trait': 'keyword',
    'override': 'modifier',
    'true false': 'atom',
    'undefined': 'null',
    Unit: 'unit',
    TermName: 'variableName',
    TermNameDecl: 'variableName definition',
    Label: 'propertyName',
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
    TraitArrow: 'punctuation definition',
    '( )': 'paren',
    '{ }': 'brace',
    '[ ]': 'squareBracket',
    '< >': 'angleBracket',
    '.': 'derefOperator',
    ', ;': 'separator',
  })
), {
  languageData: {
    closeBrackets: { brackets: ['{', '(', '[', '"'] },
    commentTokens: { line: '--', block: { open: '{-', close: '-}' } },
  }
});

document.addEventListener('DOMContentLoaded', () => {
  const output = document.getElementById('output');
  const error = document.getElementById('error');

  const UIRefresh = (element, text) => {
    element.textContent = text;
    element.innerHTML = element.innerHTML
      .replace(/^[⇣↯↓→].+$/gm, '<span class="text-secondary">$&</span>')
      .replace(/\n/g, '<br>');
  }

  const UIInterpret = (mode, state) => {
    state = state || view.state;
    output.textContent = error.textContent = '';
    try {
      UIRefresh(output, Zord.interpret(mode)(state.doc.toString())());
    } catch (err) {
      UIRefresh(error, err);
    }
  };

  const state = EditorState.create({
    extensions: [
      basicSetup,
      zordSyntax.extension,
      keymap([{ key: 'Mod-Enter', run() { UIInterpret(Zord.Verbose.value); } }]),
      ViewPlugin.fromClass(class {
        update(update) {
          if (update.docChanged) {
            UIInterpret(Zord.Simple.value, update.state);
          }
        }
      }),
    ],
  });
  const view = new EditorView({ state, parent: document.getElementById('editor') });
});
