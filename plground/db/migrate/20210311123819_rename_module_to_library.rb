class RenameModuleToLibrary < ActiveRecord::Migration[6.1]
  def change
    rename_column :docs, :require_module, :require_library
  end
end
