class HomeController < ApplicationController
  def index
    @user = current_user
  end

  def doc
    @user = current_user
    @doc = Doc.find_by(name: params[:id])
    render :index
  end
end
