class HomeController < ApplicationController
  before_action :enable_script
  before_action :set_user, only: [:user, :doc]

  def index
    @docs = Doc.where(access: [:pub, :open])
  end

  def user
    if current_user == @user
      @docs = @user.docs
    else
      @docs = Doc.where(user: @user, access: [:pub, :open])
    end
    render :index
  end

  def doc
    @doc = Doc.find_by(user: @user, name: params[:doc])
    @doc = nil if @doc && @doc.priv? && @doc.user != current_user
    if @doc
      render :index
    else
      redirect_to :root, alert: "Document '#{params[:doc]}' not found!"
    end
  end

  private
    def enable_script
      @enable_script = true
    end

    def set_user
      @user = User.find_by(username: params[:username])
      redirect_to :root, alert: "User '#{params[:username]}' not found!" unless @user
    end
end
