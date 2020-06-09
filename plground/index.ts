import 'bootstrap';
import 'bootstrap/dist/css/bootstrap.min.css';

import { EditorView } from '@codemirror/next/view';
import { EditorState } from '@codemirror/next/state';
import { keymap } from '@codemirror/next/keymap';
import { baseKeymap } from '@codemirror/next/commands';
import { lineNumbers } from '@codemirror/next/gutter';
import { foldGutter } from '@codemirror/next/fold';
import { bracketMatching } from '@codemirror/next/matchbrackets';
import { closeBrackets } from '@codemirror/next/closebrackets';
import { defaultHighlighter } from '@codemirror/next/highlight';

const state = EditorState.create({
  extensions: [
    keymap(baseKeymap),
    lineNumbers(),
    foldGutter(),
    bracketMatching(),
    closeBrackets,
    defaultHighlighter,
  ],
});
const view = new EditorView({ state });
document.getElementById('editor')!.appendChild(view.dom);

document.getElementById('run')!.onclick = () => {
  document.getElementById('output')!.append('Run button clicked. ');
};
