const Zord = bundle.Zord;

function editorState(doc, editable) {
  return bundle.editorState(doc, editable, interpret);
}

function editorView(state) {
  return bundle.editorView(state, document.getElementById('editor'));
}

function interpret() {
  $('#output').empty();
  $('#error').empty();
  const mode = $('#mode').val();
  if (mode == 'module') {
    $('#output').text('This is a module file.');
  } else {
    const run = prog => preprocess(prog).then(code => {
      $('#output').html(Zord.interpret(code)(Zord.Doc.value)());
    }).catch(err => {
      $('#error').text(err);
    });
    const code = view.state.doc.toString();
    if (mode == 'doc_only') {
      const lib = $('#require-module').val();
      fetchJson('/docs/' + lib).then(json => run(
        `${json.code} open ${json.provide_factory} in """${code}"""`
      ));
    } else { run(code); }
  }
}

function preprocess(code) {
  const regexp = /^\s*open\s+(\w+)\s*;\s*$/m;
  const found = code.match(regexp);
  if (!found) return new Promise((resolve, reject) => resolve(code));
  else return fetchDoc(found[1]).then(doc => preprocess(code.replace(regexp, doc)));
}

function fetchDoc(name) {
  return fetch('/docs/' + name).then(res => res.text())
    .catch(err => { throw new Error('Document not found: ' + name); });
}

function validate(name) {
  if (name.match(/^\w+$/) === null) {
    alert('Invalid document name (only a-z, A-Z, 0-9, and _ are allowed): ' + name);
    return false;
  } else {
    return true;
  }
}

const code = $('#code').val();
const view = editorView(editorState(code, true));
if (code) interpret();

$('#render').on('click', interpret);

$('#mode').on('change', () => {
  if ($('#mode').val() == 'module') $('#providing').removeClass('d-none').addClass('d-flex');
  else $('#providing').removeClass('d-flex').addClass('d-none');
  if ($('#mode').val() == 'doc_only') $('#requiring').removeClass('d-none').addClass('d-flex');
  else $('#requiring').removeClass('d-flex').addClass('d-none');
});
$('#mode').change();

function formData(name) {
  const data = new FormData();
  data.append('name', name);
  data.append('code', view.state.doc.toString());
  data.append('access', $('#access').val());
  data.append('mode', $('#mode').val());
  data.append('provide_factory', $('#provide-factory').val());
  data.append('require_module', $('#require-module').val());
  return data;
}

const headers = { 'X-CSRF-Token': $('meta[name="csrf-token"]').attr('content') };

$('#save').on('click', () => {
  const docname = window.location.pathname.split('/').slice(-1)[0];
  const init = { method: 'PUT', body: formData(docname), headers };
  fetch('/docs/' + docname, init).then(res => {
    $('#saved').text(res.ok ? 'Last saved: ' + new Date()
      : 'Unknown error occurred when saving...');
  }).catch(err => { $('#saved').text(err.message); });
  interpret();
});

$('#save-as').on('click', () => {
  const name = prompt('Please enter the document name to save:');
  const init = { method: 'POST', body: formData(name), headers };
  if (name && validate(name)) fetch('/docs/', init).then(res => {
    if (res.ok) window.location.assign('/' + name);
    else alert('Document name aleady occupied: ' + name);
  }).catch(err => alert(err.message));
});
