class ChangeEmailToUsername < ActiveRecord::Migration[6.1]
  def change
    add_column :users, :username, :string, null: false, default: ""
    add_index :users, :username, unique: true
    remove_column :users, :email, :string
    remove_index :docs, :name, unique: true
    add_index :docs, [:user_id, :name], unique: true
  end
end
