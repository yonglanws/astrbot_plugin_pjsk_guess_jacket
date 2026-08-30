import importlib
import sys
import types
from pathlib import Path


PLUGIN_DIR = Path(__file__).parents[1]
sys.path.insert(0, str(PLUGIN_DIR))


def _install_astrbot_stubs():
    logger = types.SimpleNamespace(
        debug=lambda *args, **kwargs: None,
        error=lambda *args, **kwargs: None,
        info=lambda *args, **kwargs: None,
        warning=lambda *args, **kwargs: None,
    )
    astrbot = types.ModuleType("astrbot")
    api = types.ModuleType("astrbot.api")
    api.logger = logger
    api.AstrBotConfig = dict
    event = types.ModuleType("astrbot.api.event")
    event.AstrMessageEvent = object
    event.filter = types.SimpleNamespace(command=lambda *args, **kwargs: lambda func: func)
    star = types.ModuleType("astrbot.api.star")
    star.Context = object
    star.Star = object
    star.StarTools = types.SimpleNamespace(get_data_dir=lambda name: Path("."))
    star.register = lambda *args, **kwargs: lambda cls: cls
    components = types.ModuleType("astrbot.api.message_components")
    core = types.ModuleType("astrbot.core")
    utils = types.ModuleType("astrbot.core.utils")
    astrbot_path = types.ModuleType("astrbot.core.utils.astrbot_path")
    astrbot_path.get_astrbot_data_path = lambda: None
    waiter = types.ModuleType("astrbot.core.utils.session_waiter")
    waiter.SessionController = object
    waiter.SessionFilter = object
    waiter.session_waiter = lambda *args, **kwargs: lambda func: func
    sys.modules.update(
        {
            "astrbot": astrbot,
            "astrbot.api": api,
            "astrbot.api.event": event,
            "astrbot.api.star": star,
            "astrbot.api.message_components": components,
            "astrbot.core": core,
            "astrbot.core.utils": utils,
            "astrbot.core.utils.astrbot_path": astrbot_path,
            "astrbot.core.utils.session_waiter": waiter,
        }
    )


def _load_main_module():
    _install_astrbot_stubs()
    sys.modules.pop("main", None)
    return importlib.import_module("main")


def test_daily_play_increments_for_existing_starter(tmp_path):
    module = _load_main_module()
    db = module.JacketDatabaseManager(str(tmp_path / "jacket.db"))

    db.update_user_play("starter", "Starter")
    db.update_user_play("starter", "Starter")

    assert db.get_user_stats("starter")[4] == 2


def test_all_effects_disabled_returns_no_effect():
    module = _load_main_module()
    processor = module.JacketEffectProcessor(
        {"effects": {name: {"enabled": False} for name in module.JacketEffectProcessor.DEFAULT_EFFECTS}}
    )

    assert processor.random_effect() == ("none", "无效果", 0)
