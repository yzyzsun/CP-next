class DocsController < ApplicationController
  before_action :set_doc, only: [:update, :destroy]

  def create
    if user_signed_in?
      doc = current_user.docs.build(doc_params)
      if doc.save
        head :ok
      else
        head :unprocessable_entity
      end
    else
      redirect_to :root, alert: "You cannot create a document unless logged in!"
    end
  end

  def show
    render plain: @doc.code
  end

  def update
    if @doc.update(doc_params)
      head :ok
    else
      head :unprocessable_entity
    end
  end

  def destory
    @doc.destroy
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
