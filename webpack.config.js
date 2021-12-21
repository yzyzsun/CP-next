const path = require('path');
const TerserPlugin = require('terser-webpack-plugin');

module.exports = {
  mode: 'production',
  entry: './app.js',
  module: {
    rules: [
      {
        test: /\.purs$/,
        exclude: /node_modules/,
        use: [
          {
            loader: 'purs-loader',
            options: {
              spago: true,
              pscIde: true,
            },
          },
        ],
      },
    ],
  },
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
    path: path.resolve(__dirname, 'backend/app/assets/javascripts'),
    library: 'bundle',
  },
};
