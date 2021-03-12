Rails.application.routes.draw do
  # For details on the DSL available within this file, see https://guides.rubyonrails.org/routing.html
  root "home#index"
  resources :docs, only: [:create, :destroy]
  get "/docs", to: "docs#show"
  put "/docs", to: "docs#update"
  devise_for :users
  get "/:username", to: "home#user"
  get "/:username/:doc", to: "home#doc"
end
