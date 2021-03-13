class RemoveCodeFromDocs < ActiveRecord::Migration[6.1]
  def change
    remove_column :docs, :code, :text, null: false
  end
end
