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
  $('#require-library').removeClass('is-invalid');
  const mode = $('#mode').val();
  if (mode == 'library') {
    $('#output').text('This is a library.');
  } else {
    const run = prog => preprocess(prog).then(code => {
      output = Zord.interpret(code)(Zord.BigStep.value)();
      if (output.startsWith('"')) output = JSON.parse(output);
      $('#output').html(output);
    }).catch(err => {
      $('#error').text(err);
      $('#error').html($('#error').html().replace(/\n/g, '<br>'));
    });
    const libErr = msg => {
      $('#require-library').addClass('is-invalid');
      $('#error').text(msg);
    };
    const code = view.state.doc.toString();
    if (mode == 'doc_only') {
      const lib = $('#require-library').val();
      if (!lib) {
        libErr('Doc-only mode requires a library.');
        return;
      }
      const arr = lib.split('/');
      const user = arr.length == 1 ? namespace : arr[0];
      const name = arr.slice(-1)[0];
      fetchDocJson(name, user).then(json => {
        if (json.mode != 'library') libErr(`'${name}' is not a library.`);
        else if (!json.provide_factory) libErr(`'${name}' does not provide a factory.`);
        else run(`${json.code} open ${json.provide_factory} in \`${code}\`.html`);
      }).catch(err => libErr(err));
    } else { run(code); }
  }
}

function preprocess(code) {
  const regexp = /open\s+(?:(\w+)\/)?(\w+)\s*;/;
  const found = code.match(regexp);
  if (!found) {
    return new Promise((resolve, reject) => resolve(code));
  } else {
    const user = found[1] || namespace;
    const name = found[2];
    return fetchDocText(name, user).then(doc =>
      preprocess(code.replace(regexp, doc.replace(/(--.*)?[\r\n]+/g, ' ')))
    );
  }
}

function fetchDoc(name, user, type, then) {
  const params = new URLSearchParams({ name, user });
  return fetch('/docs?' + params.toString(), { headers: { 'Accept': type } })
    .then(res => {
      if (res.ok) return then(res);
      else throw new Error(`Document not found: ${user}/${name}`);
    });
}

function fetchDocText(name, user) {
  return fetchDoc(name, user, 'text/plain', res => res.text());
}

function fetchDocJson(name, user) {
  return fetchDoc(name, user, 'application/json', res => res.json());
}

function validate(name) {
  if (name.match(/^\w+$/) === null) {
    alert('Invalid document name (only a-z, A-Z, 0-9, and _ are allowed): ' + name);
    return false;
  } else {
    return true;
  }
}

const namespace = window.location.pathname.split('/')[1];
const docname = window.location.pathname.split('/')[2];

const code = $('#code').val();
const view = editorView(editorState(code, true));
if (code) interpret();

$('#render').on('click', interpret);

$('#mode').on('change', () => {
  if ($('#mode').val() == 'library') $('#providing').removeClass('d-none').addClass('d-flex');
  else $('#providing').removeClass('d-flex').addClass('d-none');
  if ($('#mode').val() == 'doc_only') $('#requiring').removeClass('d-none').addClass('d-flex');
  else $('#requiring').removeClass('d-flex').addClass('d-none');
});
$('#mode').change();

function formData(name, user) {
  const data = new FormData();
  if (name) data.append('name', name);
  if (user) data.append('user', user);
  data.append('code', view.state.doc.toString());
  data.append('access', $('#access').val());
  data.append('mode', $('#mode').val());
  data.append('provide_factory', $('#provide-factory').val());
  data.append('require_library', $('#require-library').val());
  return data;
}

const headers = { 'X-CSRF-Token': $('meta[name="csrf-token"]').attr('content') };

$('#save').on('click', () => {
  const init = { method: 'PUT', body: formData(docname, namespace), headers };
  fetch('/docs', init).then(res => {
    $('#saved').text(res.ok ? 'Last saved: ' + new Date()
      : 'You are not authorized to change this document.');
  }).catch(err => { $('#saved').text(err.message); });
  interpret();
});

$('#save-as').on('click', () => {
  const name = prompt('Please enter the document name to save:');
  const init = { method: 'POST', body: formData(name), headers };
  if (name && validate(name)) fetch('/docs', init).then(res => {
    if (res.ok) res.text().then(path => { window.location.assign(path); });
    else alert('Document name aleady occupied: ' + name);
  }).catch(err => alert(err.message));
});