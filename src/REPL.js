export function require(file) {
  return function (callback) {
      return function () {
        return import(file).then(module => callback(module.main())());
      };
  };
}
