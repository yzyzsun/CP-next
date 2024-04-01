export function require(file) {
  return function (callback) {
      return function () {
        // bypass module caching to enable hot reloading
        import(file + '?t=' + Date.now())
          .then(module => callback(module.main())())
          .catch(err => console.error(err));
      };
  };
}
