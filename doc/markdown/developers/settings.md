## Settings {#settings}

As described in @ref sec::modules, each module has a settings template parameter.

### Dynamic settings

These settings are considered at compile time. For certain purposes, it is unhandy to recompile SMT-RAT for every parameter. For this, module parameters can be set
* via the command line using `--module.parameter key1=value1 --module.parameter key2=value2 ...` or
* via the `set-option` command of SMT-LIB: `(set-option :key "value")` (note that you need to pass every value as a string, even if it represents a number!).

These parameters can be accessed (most appropriately in a settings object of a module) via `int my_setting = settings_module().get("my_module.my_setting", 2)` or `std::string my_setting = settings_module().get("my_module.my_setting", "default_value")`. Note that the second parameter is the default value also specifying the type of the setting to which it is parsed.