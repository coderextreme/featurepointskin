#!/usr/bin/env python3
"""
Load an .x3d (or .wrl) file into Blender.

Run inside Blender's Text Editor / Python Console:
    import load; load.load("/path/to/model.x3d")

Or headless from a shell:
    blender --background --python load.py -- model.x3d
    blender --background --python load.py -- model.x3d --save out.blend
    blender --background --python load.py -- model.x3d --keep-scene
    blender --background --python load.py -- model.x3d --axis-forward -Z --axis-up Y
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


def load(filepath, clear=True, axis_forward="Y", axis_up="Z"):
    """Import filepath and return the list of objects it created.

    axis_forward/axis_up tell the importer how to interpret the source
    file's axes ("what direction in the X3D file is forward/up"), and get
    baked into global_matrix, which is applied rigidly to every imported
    object -- including HAnimHumanoid armatures (see
    hanim_x3d.import_humanoid(), which multiplies it straight into
    armature_obj.matrix_basis). So this one setting reorients both an
    armature's rest pose *and* all of its baked animation together.

    Blender's io_scene_x3d addon's own stock default is
    axis_forward="Z", axis_up="Y", which is correct for most plain X3D
    geometry. For this project's HAnim running-animation content that
    default left the rig lying down mid-stride instead of upright, so the
    default here is swapped to axis_forward="Y", axis_up="Z". If a
    different file needs the stock behavior, pass axis_forward="Z",
    axis_up="Y" explicitly.
    """
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
    axis_forward = argv[argv.index("--axis-forward") + 1] if "--axis-forward" in argv else "Y"
    axis_up = argv[argv.index("--axis-up") + 1] if "--axis-up" in argv else "Z"

    objects = load(filepath, clear=not keep, axis_forward=axis_forward, axis_up=axis_up)

    print(f"Imported {len(objects)} object(s) from {filepath} "
          f"(axis_forward={axis_forward}, axis_up={axis_up})")
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
