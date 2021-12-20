const namespace = window.location.pathname.split('/')[1];
const docname = window.location.pathname.split('/')[2];

function editorState(doc) {
  return bundle.editorState(doc, () => interpret(() => {}));
}

function editorView(state) {
  return bundle.editorView(state, document.getElementById('editor'));
}

const view = editorView(editorState($('#code').val()));

function interpret(callback) {
  const run = prog => preprocess(prog).then(code => {
    output = bundle.interpret(code);
    if (output.startsWith('"')) output = JSON.parse(output);
    $('#output').html(output);
    callback();
  }).catch(err => {
    $('#error').text(err);
    $('#error').html($('#error').html().replace(/\n/g, '<br>'));
    callback();
  });
  const libErr = msg => {
    $('#require-library').addClass('is-invalid');
    $('#error').text(msg);
    callback();
  };

  $('#output').empty();
  $('#error').empty();
  $('#require-library').removeClass('is-invalid');
  const code = view.state.doc.toString();
  const mode = $('#mode').val();
  if (mode == 'library') {
    run(code + '"This library has been type checked."');
  } else {
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
        if (json.mode != 'library') libErr(`'${lib}' is not a library.`);
        else if (!json.provide_factory) libErr(`'${lib}' does not provide a factory.`);
        else run(`open ${lib}; open ${json.provide_factory} in \`${code}\`.html`);
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
      preprocess(code.replace(regexp,
        doc.replace(/open\s+(\w+)\s*;/g, `open ${user}/$1;`)
           .replace(/(--.*)?[\r\n]+/g, ' ')))
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

$('#render').on('click', () => interpret(() => {}));

$('#mode').on('change', () => {
  if ($('#mode').val() == 'library') $('#providing').removeClass('d-none').addClass('d-flex');
  else $('#providing').removeClass('d-flex').addClass('d-none');
  if ($('#mode').val() == 'doc_only') {
    $('#requiring').removeClass('d-none').addClass('d-flex');
    view.dispatch({ effects: bundle.language.reconfigure([]) });
  } else {
    $('#requiring').removeClass('d-flex').addClass('d-none');
    view.dispatch({ effects: bundle.language.reconfigure(bundle.cp) });
  }
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
  data.append('html_cache', $('#output').html());
  return data;
}

const headers = { 'X-CSRF-Token': $('meta[name="csrf-token"]').attr('content') };

$('#save').on('click', () => {
  interpret(() => {
    const init = { method: 'PUT', body: formData(docname, namespace), headers };
    fetch('/docs', init).then(res => {
      $('#saved').text(res.ok ? 'Last saved: ' + new Date()
        : 'You are not authorized to change this document.');
    }).catch(err => { $('#saved').text(err.message); });
  });
});

$('#save-as').on('click', () => {
  const name = prompt('Please enter the document name to save:');
  const init = { method: 'POST', body: formData(name), headers };
  if (name && validate(name)) fetch('/docs', init).then(res => {
    if (res.ok) res.text().then(path => { window.location.assign(path); });
    else alert('Document name aleady occupied: ' + name);
  }).catch(err => alert(err.message));
});
