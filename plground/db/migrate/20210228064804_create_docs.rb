class CreateDocs < ActiveRecord::Migration[6.1]
  def change
    create_table :docs do |t|
      t.string :name
      t.index :name, unique: true
      t.text :code, null: false
      t.integer :mode, null: false
      t.string :provide_factory
      t.string :require_module

      t.timestamps
    end
  end
end
