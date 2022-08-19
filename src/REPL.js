function jseval(js) {
  return eval(js + "\n main()")
} 

export { jseval as eval }