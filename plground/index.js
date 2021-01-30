import 'bootstrap';
import 'bootstrap/dist/css/bootstrap.min.css';

import { EditorState, EditorView, basicSetup } from '@codemirror/next/basic-setup';
import { keymap } from '@codemirror/next/view';
import { styleTags, tags as t } from '@codemirror/next/highlight';
import { LanguageSupport, LezerLanguage, continuedIndent, indentNodeProp, foldNodeProp } from '@codemirror/next/language';
import { parser } from './zord';

import Zord from '../src/Zord.purs';

const zordLanguage = LezerLanguage.define({
  parser: parser.configure({
    props: [
      indentNodeProp.add({
        RecordType: continuedIndent(),
        Record: continuedIndent(),
      }),
      foldNodeProp.add({
        RecordType(tree) { return { from: tree.from + 1, to: tree.to - 1 } },
        Record(tree) { return { from: tree.from + 1, to: tree.to - 1 } },
      }),
      styleTags({
        'type extends let letrec trait implements inherits': t.definitionKeyword,
        'if then else new open in toString forall Int Double Bool String Top Bot Trait Array': t.keyword,
        'override': t.modifier,
        'true false undefined': t.atom,
        Unit: t.unit,
        TermName: t.variableName,
        TermNameDecl: t.definition(t.variableName),
        Label: t.propertyName,
        LabelDecl: t.definition(t.propertyName),
        LineComment: t.lineComment,
        BlockComment: t.blockComment,
        Number: t.number,
        String: t.string,
        HereDoc: t.docString,
        TypeOp: t.typeOperator,
        ArithOp: t.arithmeticOperator,
        LogicOp: t.logicOperator,
        CompareOp: t.compareOperator,
        MergeOp: t.operator,
        TraitArrow: t.definition(t.punctuation),
        '( )': t.paren,
        '{ }': t.brace,
        '[ ]': t.squareBracket,
        '< >': t.angleBracket,
        '.': t.derefOperator,
        ';': t.separator,
      }),
    ],
  }),
  languageData: {
    closeBrackets: { brackets: ['{', '(', '[', '"'] },
    commentTokens: { line: '--', block: { open: '{-', close: '-}' } },
  },
});

const pathname = window.location.pathname.slice(1);

const validate = name => {
  if (name.match(/^\w+$/) === null) {
    alert('Invalid document name (only a-z, A-Z, 0-9, and _ are allowed): ' + name);
    return false;
  } else {
    return true;
  }
};

const fetchDoc = name => fetch('docs/' + name).then(res => {
  if (res.ok) return res.text();
  else throw new Error('Document not found: ' + name);
});

const preprocess = code => {
  const regexp = /^\s*open\s+(\w+)\s*;\s*$/gm;
  const open = pre => {
    const match = regexp.exec(code);
    if (!match) return new Promise((resolve, reject) => resolve(pre));
    else return fetchDoc(match[1]).then(doc => open(pre + doc));
  };
  return open('').then(pre =>
    new Promise((resolve, reject) => resolve(pre + code.replace(regexp, '')))
  );
};

document.addEventListener('DOMContentLoaded', () => {
  const output = document.getElementById('output');
  const error = document.getElementById('error');

  const interpret = () => {
    output.textContent = error.textContent = '';
    preprocess(view.state.doc.toString()).then(code => {
      const text = Zord.interpret(code)(Zord.Doc.value)();
      output.innerHTML = text;
    }).catch(err => {
      error.textContent = err;
      error.innerHTML = element.innerHTML
        .replace(/^[⇣↯↓→].+$/gm, '<span class="text-secondary">$&</span>')
        .replace(/\n/g, '<br>');
    });
  };

  const state = (doc, editable) => EditorState.create({
    doc,
    extensions: [
      basicSetup,
      EditorView.lineWrapping,
      EditorView.editable.of(editable),
      keymap.of([{ key: 'Mod-Enter', run: interpret }]),
      new LanguageSupport(zordLanguage),
    ],
  });

  const view = new EditorView({
    state: pathname ? state('loading...', false) : state('', true),
    parent: document.getElementById('editor'),
  });

  if (pathname) fetchDoc(pathname).then(doc => {
    view.setState(state(doc, true));
    if (/^--\s*module/.test(doc)) output.textContent = "This is a module file.";
    else interpret();
  }).catch(err => {
    alert(err.message);
    window.location.replace('/');
  });
  else fetch('/docs').then(res => res.text()).then(text =>{
    output.innerHTML += text;
  });

  document.getElementById('title').onclick = () => {
    const name = prompt('Please enter which document to go (blank to go home):');
    if (name === '' || name && validate(name)) {
      window.location.assign('/' + name);
    }
    return false;
  };

  document.getElementById('render').onclick = interpret;

  document.getElementById('save').onclick = () => {
    const name = prompt('Please enter the document name to save:');
    const init = { method: 'POST', body: view.state.doc.toString() };
    if (name && validate(name)) fetch('docs/' + name, init).then(res => {
      if (res.ok) window.location.assign('/' + name);
      else alert('Document name aleady occupied: ' + name);
    }).catch(err => alert(err.message));
  };
});
