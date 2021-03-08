class DocsController < ApplicationController
  before_action :set_doc, only: [:show, :destroy]

  def create
    if user_signed_in?
      doc = current_user.docs.build(doc_params)
      if doc.save
        doc.path
      else
        head :unprocessable_entity
      end
    else
      redirect_to :root, alert: "You cannot create a document unless logged in!"
    end
  end

  def show
    respond_to do |format|
      format.text { render plain: @doc.code }
      format.json
    end
  end

  def destroy
    @doc.destroy
    redirect_to :root
  end

  def update
    user = User.find_by(username: params[:username])
    doc = Doc.find_by(user: user, name: params[:doc])
    if doc.open? || doc.user == current_user
      if doc.update(doc_params)
        head :ok
      else
        head :unprocessable_entity
      end
    else
      head :unauthorized
    end
  end

  private
    def set_doc
      @doc = Doc.find_by(user: current_user, name: params[:id])
      head :not_found unless @doc
    end

    def doc_params
      params.permit(:name, :code, :access, :mode, :provide_factory, :require_module)
    end
end
