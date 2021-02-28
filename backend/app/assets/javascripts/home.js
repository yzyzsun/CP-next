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
  return fetchJson('/docs/' + name).then(json => json.code)
    .catch(err => { throw new Error('Document not found: ' + name); });
}

function fetchJson(url) {
  return fetch(url).then(res => res.json());
}

function validate(name) {
  if (name.match(/^\w+$/) === null) {
    alert('Invalid document name (only a-z, A-Z, 0-9, and _ are allowed): ' + name);
    return false;
  } else {
    return true;
  }
}

const headers = { 'X-CSRF-Token': $('meta[name="csrf-token"]').attr('content') };

const pathname = window.location.pathname.slice(1);

const view = editorView(
  pathname ? editorState('loading...', false) : editorState('', true)
);

if (pathname) fetchJson('/docs/' + pathname).then(json => {
  view.setState(editorState(json.code, true));
  $('#access').val(json.access);
  $('#mode').val(json.mode);
  $('#mode').change();
  $('#provide-factory').val(json.provide_factory);
  $('#require-module').val(json.require_module);
  interpret();
}).catch(err => {
  alert('Document not found; redirecting to home page');
  window.location.replace('/');
}); else fetchJson('/docs').then(json => {
  $('#output').append('<ul>');
  for (const name of json.sort()) {
    $('#output').append(`<li><a href="/${name}">${name}</a></li>`);
  }
  $('#output').append('</ul>');
  $('#save').prop('disabled', true);
});

$('#render').on('click', interpret);

$('#mode').on('change', () => {
  if ($('#mode').val() == 'module') $('#providing').removeClass('d-none');
  else $('#providing').addClass('d-none');
  if ($('#mode').val() == 'doc_only') $('#requiring').removeClass('d-none');
  else $('#requiring').addClass('d-none');
});

function modal(prep) {
  $('#modal-sign .modal-body').load('/users/sign_' + prep, () => {
    $('#modal-sign a').hide();
    $('#modal-sign').modal('show');
  });
  return false;
}

$('#login').on('click', () => modal('in'));
$('#signup').on('click', () => modal('up'));

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

$('#save').on('click', () => {
  const init = { method: 'PUT', body: formData(pathname), headers };
  fetch('/docs/' + pathname, init).then(res => {
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
