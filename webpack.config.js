const path = require('path');

module.exports = {
  mode: 'development',
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
  performance: { hints: false },
  output: {
    filename: 'bundle.js',
    path: path.resolve(__dirname, 'backend/app/assets/javascripts'),
    library: 'bundle',
  },
  resolve: {
    fallback: {
      fs: false
    }
  }
};
