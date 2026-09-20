#!/usr/bin/env python3
"""
Load an .x3d (or .wrl) file into Blender.

Run inside Blender's Text Editor / Python Console:
    import load; load.load("/path/to/model.x3d")

Or headless from a shell:
    blender --background --python load.py -- model.x3d
    blender --background --python load.py -- model.x3d --save out.blend
    blender --background --python load.py -- model.x3d --keep-scene
"""

import os
import sys

import addon_utils
import bpy

CANDIDATE_MODULES = (
    "io_scene_x3d",
    "bl_ext.blender_org.io_scene_x3d",
    "bl_ext.user_default.io_scene_x3d",
)


def ensure_importer():
    """Enable whichever io_scene_x3d module this Blender has. Returns its name."""
    if hasattr(bpy.ops.import_scene, "x3d"):
        return "already registered"

    for module in CANDIDATE_MODULES:
        try:
            addon_utils.enable(module, default_set=False, persistent=False)
        except Exception:
            continue
        if hasattr(bpy.ops.import_scene, "x3d"):
            return module

    raise RuntimeError(
        "The X3D importer is not available. In Blender 4.2+ install it from "
        "Edit > Preferences > Get Extensions and search for 'Web3D X3D/VRML'."
    )


def clear_scene():
    """Delete every object in the current scene."""
    bpy.ops.object.select_all(action="SELECT")
    bpy.ops.object.delete(use_global=False)


def load(filepath, clear=True, axis_forward="Z", axis_up="Y"):
    """Import filepath and return the list of objects it created."""
    filepath = os.path.abspath(os.path.expanduser(filepath))
    if not os.path.isfile(filepath):
        raise FileNotFoundError(filepath)

    ensure_importer()

    if clear:
        clear_scene()

    before = set(bpy.data.objects)
    result = bpy.ops.import_scene.x3d(
        filepath=filepath,
        axis_forward=axis_forward,
        axis_up=axis_up,
    )
    if "FINISHED" not in result:
        raise RuntimeError(f"Import did not finish: {result}")

    return [obj for obj in bpy.data.objects if obj not in before]


def main(argv):
    if "--" in argv:
        argv = argv[argv.index("--") + 1:]
    else:
        argv = []

    if not argv:
        print(__doc__)
        return 1

    filepath = argv[0]
    keep = "--keep-scene" in argv
    save_to = None
    if "--save" in argv:
        save_to = argv[argv.index("--save") + 1]

    objects = load(filepath, clear=not keep)

    print(f"Imported {len(objects)} object(s) from {filepath}")
    for obj in objects:
        verts = len(obj.data.vertices) if obj.type == "MESH" else 0
        print(f"  {obj.name:<40} {obj.type:<10} {verts} verts")

    if save_to:
        save_to = os.path.abspath(os.path.expanduser(save_to))
        bpy.ops.wm.save_as_mainfile(filepath=save_to)
        print(f"Saved {save_to}")

    return 0


if __name__ == "__main__":
    main(list(sys.argv))
