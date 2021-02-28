Rails.application.routes.draw do
  # For details on the DSL available within this file, see https://guides.rubyonrails.org/routing.html
  root "home#index"
  resources :docs, except: [:new, :edit]
  devise_for :users
  get "/:id", to: "home#doc"
end
