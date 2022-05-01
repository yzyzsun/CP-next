const path = require('path');
const TerserPlugin = require('terser-webpack-plugin');

module.exports = {
  mode: 'production',
  entry: './app.js',
  resolve: {
    fallback: {
      fs: false,
    },
  },
  optimization: {
    minimizer: [new TerserPlugin({
      extractComments: false,
    })],
  },
  performance: { hints: false },
  output: {
    filename: 'bundle.js',
    path: path.resolve(__dirname, 'plground/app/assets/javascripts'),
    library: 'bundle',
  },
};
