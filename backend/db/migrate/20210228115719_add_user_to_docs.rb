class AddUserToDocs < ActiveRecord::Migration[6.1]
  def change
    add_column :docs, :access, :integer, null: false
    add_reference :docs, :user, foreign_key: true
  end
end
