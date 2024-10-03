import sounddevice as sd
import numpy as np
import time
import pyglet
from pyglet import shapes
from collections import deque
import colorsys
import logging
import tkinter as tk
from tkinter import ttk
import sys
import atexit
import webbrowser
import math
from math import sin, cos, radians
from lifxlan import LifxLAN, Light, WorkflowException
import platform
import pygame
# Build 023.001 24-09-2024

# Constants for audio processing
RATE = 44100
BUFFER = 512
TARGET_FREQS = [35, 40, 45, 50, 55]  # Multiple target frequencies
SMOOTHING_WINDOW = 10
UPDATE_INTERVAL = 1 / 240  # Interval in seconds for updating brightness
SENSITIVITY_MULTIPLIER = 1.0  # Multiplier to make the visualizer more sensitive
NUM_ORBS = 25  # Number of orbs
WAVEFORM_POINTS = 28  # Number of points for waveform mode
SPECTRUM_BARS = 30  # Number of bars for spectrum mode
BRIGHTNESS_FONT_SIZE = 56  # Font size for the brightness text
GITHUB_FONT_SIZE = 10  # Font size for the GitHub link text
GITHUB_TRANSPARENCY = 145  # Text transparency (150%)
HORIZONTAL_ADJUSTMENT = 0  # Horizontal adjustment constant for the orbs
SHAKE_INTENSITY = 10  # Maximum shake intensity
BLACK_HOLE_STRENGTH = 0.07  # Strength of the black hole effect
PULL_FROM_CENTER = True  # If True, pull orbs from the center outward; if False, pull orbs from the edges inward
ESCAPE_MODE = False  # If True, orbs escape randomly

# Variables for FPS calculation
last_frame_time = time.time()
last_fps_update_time = time.time()
displayed_fps = 0.0
fps_visible = True # Global variable to track if FPS is visible

#Github
global github_label  # Make sure this is at the start of the code
github_label = None  # Initialize it as None

#Spectrum bar constant
MARGIN_CONSTANT = 1  # Adjust this value to control the margins from the sides

# Global buffer for storing the latest audio data
latest_audio_data = None
# Initialize waveform_data
waveform_data = []

# Framerate
FPS_CAP = 70

# Decay Constants
INITIAL_DECAY_RATE = 0.5  # Start decay rate in dB
MAX_DECAY_RATE = 5  # Maximum decay rate in dB
DECAY_RAMP_UP_INTERVAL = 1.5  # Time in seconds after which decay rate increases

# Constants for sensitivity
WAVEFORM_SENSITIVITY = 1.0  # Default sensitivity for Waveform mode
SPECTRUM_SENSITIVITY = 1.0  # Default sensitivity for Spectrum Bars mode

# Increase the EMA smoothing factor for the waveform
WAVEFORM_SMOOTHING_FACTOR = 0.025  # More aggressive smoothing for the waveform
SPECTRUM_SMOOTHING_FACTOR = 0.025 # More aggressive smoothing for the spectrum bars

# Modify the brightness smoothing factor for more gradual transitions
BRIGHTNESS_SMOOTHING_FACTOR = 0.05  # Slower brightness change
BRIGHTNESS_DECAY_FACTOR = 0.2  # Increased decay to avoid lingering brightness

# Global variable to store current sensitivity
current_sensitivity = SENSITIVITY_MULTIPLIER

# Constants for GUI layout
MENU_WIDTH = 140
MENU_HEIGHT = 220  # Adjusted to fit all menu items
MENU_PADDING = 5
TEXT_HEIGHT = 10
TEXT_PADDING = 10
BOTTOM_MARGIN = 30  # Margin from the bottom of the window

# Additional constants for positioning
LABEL_X_OFFSET = 50
VALUE_X_OFFSET = 0
ROW_HEIGHT = 30
TEXT_SIZE = 12

# Default positions for the control menu
MENU_X = 690
MENU_Y = 225

# Constants for radial dB meters with a bouncing effect
DEFAULT_NUM_BARS = 62  # Number of bars in the radial dB meter
DEFAULT_BAR_WIDTH = 5  # Default width of each bar
DEFAULT_MAX_BAR_LENGTH = 350  # Maximum length of the bars
DEFAULT_RADIUS = 150  # Default radius for the circle
ANGLE_INCREMENT = 360 / DEFAULT_NUM_BARS  # Each bar's angular separation in degrees
BOUNCE_INTENSITY = 110  # Intensity of the bounce effect

# Constants for the improved diamond cut effect
DIAMOND_SIZE = 35 # Base size for the diamonds (adjust as needed)
DIAMOND_POWER = 110  # How much the triangles move apart based on brightness/glow_value

# Constants for the polygon circle
NUM_SIDES = 24  # Number of sides to approximate the circle
OUTLINE_THICKNESS = 5  # Thickness of the outline (adjustable)
INNER_CIRCLE_RADIUS = 140  # Inner radius of the circle (adjustable)

# Define the new constants for triangle sizes and distances
TRIANGLE_1_SIZE = 20  # Size of the first smaller triangle
TRIANGLE_1_DISTANCE = 50  # Distance of the first smaller triangle from the main triangle

TRIANGLE_2_SIZE = 15  # Size of the second smaller triangle
TRIANGLE_2_DISTANCE = 30  # Distance of the second smaller triangle from the first one

TRIANGLE_3_SIZE = 10  # Size of the third smaller triangle
TRIANGLE_3_DISTANCE = 20  # Distance of the third smaller triangle from the second one

DRAW_SMALL_TRIANGLES = True  # Set to False if you don't want to draw the smaller triangles

LIFX_IP = ""  # IP address of your LIFX light
LIFX_MAC = ""  # MAC address of your LIFX light
lifx = LifxLAN()
bulb = None
#bulb = Light(LIFX_MAC, LIFX_IP)  # Use the specific IP and MAC to control the light

# Separate packet send rate for LIFX (in seconds)
PACKET_SEND_INTERVAL = 0.01  # Send packets to the light every 0.1 seconds

# Minimum dB value to avoid bars going below zero
MIN_DB = -100  # Adjust this value as needed
current_gain_db_smoothed = -100

# Easter egg sequence detection
easter_egg_sequence = "rgb"
current_sequence = ""

# Set up logging
logging.basicConfig(level=logging.ERROR)

# Pyglet window setup
window = pyglet.window.Window(width=900, height=600, caption='Visual Bass Sync v023.001 24-09-2024', resizable=True)
batch = pyglet.graphics.Batch()

# Check if we're on macOS
if platform.system() == "Darwin":
    # Use the default input device (set in macOS System Preferences)
    default_input_device = sd.default.device[0]  # [0] is input, [1] is output
    print(f"Using default input device: {default_input_device}")
else:
    # For other platforms, select manually or default
    default_input_device = None  # None will automatically use the system default device
    print("Using input device for non-macOS platforms.")

# Start the audio stream using the default device
try:
    stream = sd.InputStream(device=default_input_device, samplerate=44100, channels=1)
    stream.start()
    print("Audio stream started.")
except Exception as e:
    print(f"Failed to start audio stream: {e}")


# Platform-specific adjustments
if platform.system() == "Darwin":
    # To properly scale the window for Retina displays
    def retina_scale():
        return window.get_pixel_ratio()  # Will return a ratio (typically 2.0 on Retina)


    pixel_ratio = retina_scale()

    # Resize window based on the pixel ratio for Retina displays
    window.set_size(int(window.width * pixel_ratio), int(window.height * pixel_ratio))

# Variables for audio data
smoothed_value = 0
glow_value = 0
current_glow_value = 0
smoothing_buffer = deque(maxlen=SMOOTHING_WINDOW)
last_max_time = time.time()
last_update_time = time.time()
current_gain_db = MIN_DB  # Initialize to a minimum dB value
hue = 0
manual_hue = False  # Flag for manual hue setting
control_menu_visible = False  # Flag to track control menu visibility

# Variables for control settings
control_hue = 0
control_speed = 0.0004
control_gravity = BLACK_HOLE_STRENGTH
control_orb_amount = NUM_ORBS
control_waveform_points = WAVEFORM_POINTS  # Default points for waveform
control_spectrum_bars = SPECTRUM_BARS  # Default bars for spectrum
control_sensitivity = SENSITIVITY_MULTIPLIER
control_brightness_floor = 0.0  # Brightness floor as a percentage
visualization_mode = "Black Hole"  # Start with Black Hole mode

# Variables to track the last time a packet was sent to the light
last_packet_time = time.time()  # Ensure it's initialized

# Function to send color to LIFX light with retry mechanism
def send_lifx_color(brightness, hue, retries=3):
    if bulb is None:

        return

    # Convert hue to LIFX scale (0-65535)
    hue_value = int(hue * 65535) % 65535  # Ensure hue is within 0-65535
    saturation = 65535
    brightness_value = int(max(brightness, control_brightness_floor) * 65535)
    kelvin = 3500

    # Attempt to send color to LIFX bulb with retries
    for attempt in range(retries):
        try:
            bulb.set_color([hue_value, saturation, brightness_value, kelvin])
            logging.info(f"Sent color to LIFX: hue={hue_value}, brightness={brightness_value}")
            return
        except AttributeError as e:
            logging.error(f"AttributeError on attempt {attempt + 1}: {e}")
            time.sleep(0.1)  # Short delay before retrying
        except WorkflowException as e:
            logging.error(f"WorkflowException on attempt {attempt + 1}: {e}")
            time.sleep(0.1)  # Short delay before retrying
        except Exception as e:
            logging.error(f"Unexpected exception on attempt {attempt + 1}: {e}")
            time.sleep(0.1)  # Short delay before retrying

    logging.error(f"Failed to send color to LIFX after {retries} attempts")
#

# Function to detect target frequencies
def detect_frequencies(data, rate, target_freqs):
    try:
        data = np.ascontiguousarray(data)  # Ensure the array is contiguous
        freqs = np.fft.fftfreq(len(data), 1 / rate)
        fft_data = np.abs(np.fft.fft(data))
        detected_values = []
        for target_freq in target_freqs:
            target_index = np.argmin(np.abs(freqs - target_freq))
            detected_values.append(fft_data[target_index])
        return max(detected_values)
    except Exception as e:
        logging.error(f"Error in detect_frequencies: {e}")
        return 0
#

latest_audio_data = None
glow_value = 0.0
smoothing_buffer = []
last_max_time = 0
last_update_time = time.time()
current_glow_value = 0.0
smoothed_value = 0.0
current_gain_db = 0.0
current_gain_db_smoothed = 0.0
hue = 0  # Define as needed
last_packet_time = time.time()


def smooth_db_value(new_db, smoothing_factor=0.1):
    """
    Smooth the decibel value to prevent sudden drops.

    :param new_db: The new decibel value.
    :param smoothing_factor: The factor for smoothing (0 < smoothing_factor < 1).
    """
    global current_gain_db_smoothed
    if current_gain_db_smoothed is None:
        current_gain_db_smoothed = new_db
    else:
        current_gain_db_smoothed = (smoothing_factor * new_db + (1 - smoothing_factor) * current_gain_db_smoothed)

# Audio callback function
def audio_callback(indata, frames, time_info, status):
    global waveform_data, latest_audio_data, glow_value, smoothing_buffer, last_max_time
    global last_update_time, current_glow_value, smoothed_value, current_gain_db
    global current_gain_db_smoothed, hue, last_packet_time

    try:
        if status:
            logging.warning(status)

        waveform_data = indata[:, 0]  # Assuming mono channel (1D array)
        latest_audio_data = indata[:, 0]  # Assuming mono channel (1D array)

        current_time = time.time()

        # Peak level detection
        peak_value = np.max(np.abs(indata[:, 0]))  # Detect the peak value
        new_db = 20 * np.log10(peak_value) if peak_value > 0 else -100  # Convert peak value to dB

        # Smooth the dB value to prevent sudden drops (optional)
        smooth_db_value(new_db)

        detection_value = detect_frequencies(indata[:, 0], RATE, TARGET_FREQS)  # Use only the first channel
        smoothing_buffer.append(detection_value)
        if len(smoothing_buffer) > 10:  # Limit buffer size
            smoothing_buffer.pop(0)
        smoothed_value = sum(smoothing_buffer) / len(smoothing_buffer)

        # Adjust the new_glow_value with sensitivity
        new_glow_value = min((smoothed_value / 100) * control_sensitivity, 1.0)

        if current_time - last_update_time >= UPDATE_INTERVAL:
            if new_glow_value >= 1.0:
                last_max_time = current_time
            current_glow_value = new_glow_value * control_sensitivity  # Apply sensitivity
            last_update_time = current_time

        glow_value = current_glow_value

        # Update LIFX color based on the separate packet rate
        if current_time - last_packet_time >= PACKET_SEND_INTERVAL:
            send_lifx_color(glow_value, hue)
            last_packet_time = current_time

    except Exception as e:
        logging.error(f"Error in audio_callback: {e}")
#

# Start audio stream
def start_audio_stream(input_device_index):
    global stream
    try:
        stream = sd.InputStream(samplerate=RATE, blocksize=BUFFER, channels=1, callback=audio_callback,
                                device=input_device_index)
        stream.start()
    except Exception as e:
        logging.error(f"Failed to start audio stream: {e}")
        sys.exit(1)
#

# Variables for 3D visualization
orbs = []

def create_orbs_or_waveform_points(num):
    global orbs, control_waveform_points, control_spectrum_bars
    try:
        if visualization_mode == "Black Hole":
            orbs = []
            for i in range(num):
                orb = shapes.Circle(x=window.width // 2 + HORIZONTAL_ADJUSTMENT, y=window.height // 2, radius=18,
                                    color=(255, 255, 255), batch=batch)
                orbs.append(orb)
        elif visualization_mode == "Waveform":
            control_waveform_points = num  # Store the waveform points value
        elif visualization_mode == "Spectrum Bars":
            control_spectrum_bars = num  # Store the spectrum bars value
    except Exception as e:
        logging.error(f"Error in create_orbs_or_waveform_points: {e}")
#

class EditableField:
    def __init__(self, label, x, y, width=70, height=20, initial_value=""):
        self.label = pyglet.text.Label(label, font_size=10, x=x, y=y + 20, anchor_x='left', anchor_y='center',
                                       color=(255, 255, 255, 255))
        self.text = pyglet.text.Label(initial_value, font_size=10, x=x + width // 2, y=y, anchor_x='center',
                                      anchor_y='center', color=(255, 255, 255, 255))
        self.value = initial_value
        self.width = width
        self.height = height
        self.x = x
        self.y = y
        self.active = False
        self.hover = False  # Track whether the mouse is hovering

    def draw(self):
        # Background color changes if hovered or active
        if self.active:
            glow_color = (0, 100, 139)  # Dark cyan when active
        elif self.hover:
            glow_color = (0, 255, 255)  # Bright cyan when hovered
        else:
            glow_color = (50, 50, 50)  # Default background color

        # Position background directly under the editable field (text box)
        background = shapes.Rectangle(self.text.x - self.width // 2, self.y - self.height // 2, self.width, self.height,
                                      color=glow_color, batch=batch)
        background.opacity = 180
        background.draw()

        # Draw label and text
        self.label.draw()
        self.text.draw()

    def hit_test(self, x, y):
        # Test hit directly on the text field, not the label
        return self.text.x - self.width // 2 < x < self.text.x + self.width // 2 and self.y - self.height // 2 < y < self.y + self.height // 2

    def set_active(self, active):
        self.active = active

    def set_hover(self, hover):
        self.hover = hover

    def set_value(self, value):
        self.value = value
        self.text.text = value

    def update_position(self, x, y):
        self.x = x
        self.y = y
        self.label.x = x - self.width // 2
        self.label.y = y + 20
        self.text.x = x + self.width // 2
        self.text.y = y
#

# Initialize Pygame and create the surface only once
def init_pygame_surface():
    global pygame_surface
    # Create a Pygame surface (off-screen)
    pygame_surface = pygame.Surface((800, 600))  # This surface is off-screen

    pygame.init()

def pygame_to_pyglet_texture(pygame_surface):
    # Convert the Pygame surface to a string format suitable for Pyglet
    data_string = pygame.image.tostring(pygame_surface, 'RGBA', False)
    # Create a Pyglet image from the Pygame surface
    image = pyglet.image.ImageData(pygame_surface.get_width(), pygame_surface.get_height(), 'RGBA', data_string)
    return image.get_texture()

@window.event
def on_draw():
    global last_frame_time, last_fps_update_time, displayed_fps, fps_visible, control_label

    # Clear the Pyglet window before drawing
    window.clear()

    # Check for different visualization modes and handle them accordingly
    if visualization_mode == "Black Hole":
        draw_gain_bars()
        for orb in orbs:
            orb.draw()
    elif visualization_mode == "Waveform":
        draw_waveform()
    elif visualization_mode == "Spectrum Bars":
        draw_spectrum_bars()
    elif visualization_mode == "Radial dB Meters":
        draw_radial_db_meters()
    elif visualization_mode == "Polygon":
        draw_polygon_mode(pygame_surface, glow_value, hue, center_x, center_y) # Use Pygame for off-screen rendering
        pyglet_texture = pygame_to_pyglet_texture(pygame_surface) # Convert Pygame surface to Pyglet texture and blit it
        pyglet_texture.blit(0, 0, width=SCREEN_WIDTH, height=SCREEN_HEIGHT) # Use hardcoded 800x600
        #draw_gain_bars() # Now draw the dB meters on top of the cube

    # Draw text, control labels, FPS, etc.
    draw_text()
    draw_control_label()

    if fps_visible:
        draw_fps()

    if control_menu_visible:
        draw_control_menu()
#

def draw_fps():
    global last_frame_time, last_fps_update_time, displayed_fps

    # Calculate the time between frames
    current_time = time.time()
    delta_time = current_time - last_frame_time
    last_frame_time = current_time

    # Update the FPS counter every second
    if current_time - last_fps_update_time >= 0.2:
        displayed_fps = int(1.0 / delta_time)
        last_fps_update_time = current_time

    # Display the FPS
    fps_label = pyglet.text.Label(f"FPS: {displayed_fps}", font_size=12, x=10, y=window.height - 10,
                                  anchor_x='left', anchor_y='center', color=(255, 255, 255, 255))
    fps_label.draw()
#

def draw_control_label():
    global control_label
    try:
        # Create the control label to toggle the menu (bottom-right corner)
        control_label = pyglet.text.Label("Control Menu",
                                          font_size=10,
                                          x=window.width - 10,  # Right-align
                                          y=10,  # Bottom-left corner
                                          anchor_x='right', anchor_y='bottom',
                                          color=(255, 255, 255, 150))  # White text with transparency
        control_label.draw()

    except Exception as e:
        logging.error(f"Error in draw_control_label: {e}")
#

def update_cube_position_and_scale(width, height):
    global center_x, center_y

    # Recalculate the center of the window
    center_x = width // 2
    center_y = height // 2

    # Adjust the cube scaling based on window size
    max_dimension = min(width, height)
    global DEFAULT_SCALE_FACTOR
    DEFAULT_SCALE_FACTOR = max_dimension / 5  # Adjust the scale factor to fit within the new window size
#

@window.event
def on_resize(width, height):
    global center_x, center_y  # Recalculate the global center coordinates
    try:
        # Recalculate the center of the window
        center_x = width // 2
        center_y = height // 2

        # Update orb positions
        for orb in orbs:
            orb.x = center_x
            orb.y = center_y

        # Adjust scaling or repositioning logic based on new window size
        align_control_menu()

        # Handle cube scaling and position, ensuring it's within the screen bounds
        update_cube_position_and_scale(width, height)

    except Exception as e:
        logging.error(f"Error in on_resize: {e}")


#

@window.event
def on_mouse_motion(x, y, dx, dy):
    try:
        global hue_field, speed_field, gravity_field, orbs_field, sensitivity_field, brightness_floor_field, mode_toggle_field
        # Check for hover state in each menu field
        mode_toggle_field.set_hover(mode_toggle_field.hit_test(x, y))
        hue_field.set_hover(hue_field.hit_test(x, y))
        speed_field.set_hover(speed_field.hit_test(x, y))
        gravity_field.set_hover(gravity_field.hit_test(x, y))
        orbs_field.set_hover(orbs_field.hit_test(x, y))
        sensitivity_field.set_hover(sensitivity_field.hit_test(x, y))
        brightness_floor_field.set_hover(brightness_floor_field.hit_test(x, y))
    except Exception as e:
        logging.error(f"Error in on_mouse_motion: {e}")
#

@window.event
def on_mouse_press(x, y, button, modifiers):
    global fps_visible, control_label, github_label  # Make fps_visible, control_label, and github_label accessible
    try:
        if button == pyglet.window.mouse.LEFT:
            # Toggle FPS display if FPS label is clicked
            if 10 < x < 100 and window.height - 30 < y < window.height - 10:  # FPS label position range
                fps_visible = not fps_visible

            # Check if control_label exists before accessing it
            if control_label is not None:
                # Check if the click is within the control menu toggle area
                if control_label.x - 100 < x < control_label.x + control_label.content_width and \
                        control_label.y - 20 < y < control_label.y + control_label.content_height:
                    toggle_control_menu()

            # Process clicks within the control menu if it's visible
            if control_menu_visible:
                process_control_menu_click(x, y)

            # Check if the click is on the Black Hole, Waveform, or Spectrum Bars toggle
            if mode_toggle_field is not None and mode_toggle_field.hit_test(x, y):
                toggle_visualization_mode()

            # Check if the GitHub label exists before trying to access it
            if github_label is not None:
                # Check if the click is on the GitHub label
                if github_label.x < x < github_label.x + github_label.content_width and \
                        github_label.y - 20 < y < github_label.y + github_label.content_height:
                    webbrowser.open("https://github.com/Fklyf/VisualBassSync")

    except Exception as e:
        logging.error(f"Error in on_mouse_press: {e}")
#

@window.event
def on_text(text):
    try:
        global hue_field, speed_field, gravity_field, orbs_field, sensitivity_field, brightness_floor_field
        if mode_toggle_field.active:
            mode_toggle_field.set_value(mode_toggle_field.value + text)
        elif hue_field.active:
            hue_field.set_value(hue_field.value + text)
        elif speed_field.active:
            if text.isdigit() or text == '.':
                speed_field.set_value(speed_field.value + text)
        elif gravity_field.active:
            gravity_field.set_value(gravity_field.value + text)
        elif orbs_field.active:
            orbs_field.set_value(orbs_field.value + text)
        elif sensitivity_field.active:
            sensitivity_field.set_value(sensitivity_field.value + text)
        elif brightness_floor_field.active:
            brightness_floor_field.set_value(brightness_floor_field.value + text)
    except Exception as e:
        logging.error(f"Error in on_text: {e}")
#

@window.event
def on_key_press(symbol, modifiers):
    try:
        global hue_field, speed_field, gravity_field, orbs_field, sensitivity_field, brightness_floor_field
        if symbol == pyglet.window.key.BACKSPACE:
            if mode_toggle_field.active:
                mode_toggle_field.set_value(mode_toggle_field.value[:-1])
            elif hue_field.active:
                hue_field.set_value(hue_field.value[:-1])
            elif speed_field.active:
                speed_field.set_value(speed_field.value[:-1])
            elif gravity_field.active:
                gravity_field.set_value(gravity_field.value[:-1])
            elif orbs_field.active:
                orbs_field.set_value(orbs_field.value[:-1])
            elif sensitivity_field.active:
                sensitivity_field.set_value(sensitivity_field.value[:-1])
            elif brightness_floor_field.active:
                brightness_floor_field.set_value(brightness_floor_field.value[:-1])
        elif symbol == pyglet.window.key.ENTER:
            if mode_toggle_field.active:
                toggle_visualization_mode()
                mode_toggle_field.set_active(False)
            elif hue_field.active:
                apply_hue_setting()
                hue_field.set_active(False)
            elif speed_field.active:
                apply_speed_setting()
                speed_field.set_active(False)
            elif gravity_field.active:
                apply_gravity_setting()
                gravity_field.set_active(False)
            elif orbs_field.active:
                apply_orbs_setting()
                orbs_field.set_active(False)
            elif sensitivity_field.active:
                apply_sensitivity_setting()
                sensitivity_field.set_active(False)
            elif brightness_floor_field.active:
                apply_brightness_floor_setting()
                brightness_floor_field.set_active(False)
        else:
            global current_sequence, ESCAPE_MODE
            key = chr(symbol)
            current_sequence += key
            if easter_egg_sequence in current_sequence:
                current_sequence = ""
                ESCAPE_MODE = not ESCAPE_MODE
                print("Easter egg activated! Toggled escape mode.")
    except Exception as e:
        logging.error(f"Error in on_key_press: {e}")
#

def create_orbs(num_orbs):
    global orbs
    try:
        orbs = []
        for i in range(num_orbs):
            orb = shapes.Circle(x=window.width // 2, y=window.height // 2, radius=18,
                                color=(255, 255, 255), batch=batch)
            orbs.append(orb)
    except Exception as e:
        logging.error(f"Error in create_orbs: {e}")
#

def toggle_visualization_mode():
    global visualization_mode, orbs_field, mode_toggle_field, control_waveform_points, control_spectrum_bars, orbs

    if visualization_mode == "Black Hole":
        visualization_mode = "Waveform"
        mode_toggle_field.set_value("Waveform")
        orbs_field.label.text = "Waveform Points:"
        orbs_field.set_value(str(control_waveform_points))
        orbs.clear()  # Clear the orbs since we're switching to waveform mode
    elif visualization_mode == "Waveform":
        visualization_mode = "Spectrum Bars"
        mode_toggle_field.set_value("Spectrum")
        orbs_field.label.text = "Spectrum Bars:"
        orbs_field.set_value(str(control_spectrum_bars))  # Use the same control for bars
        orbs.clear()  # Clear the orbs since we're switching to spectrum bars mode
    elif visualization_mode == "Spectrum Bars":
        visualization_mode = "Radial dB Meters"
        mode_toggle_field.set_value("Radial")
        orbs_field.label.text = "dB Meter Points:"
        orbs_field.set_value(str(None))
        orbs.clear()  # Clear for radial dB meter mode

    elif visualization_mode == "Spectrum Bars":
        # Switch to Radial dB Meters Mode
        visualization_mode = "Radial dB Meters"
        mode_toggle_field.set_value("Radial")
        orbs_field.label.text = "dB Meter Points:"
        orbs_field.set_value(str(None))  # No points to control here
        orbs.clear()  # Clear orbs since they're not needed in this mode

    elif visualization_mode == "Radial dB Meters":
        # Switch to Polygon Mode
        visualization_mode = "Polygon"
        mode_toggle_field.set_value("Polygon")
        orbs_field.label.text = "Polygon Sides:"
        orbs_field.set_value(str(None))  # Set the number of sides for the polygon
        orbs.clear()  # Clear orbs for this mode if needed

    else:
        # Switch back to Black Hole Mode (default)
        visualization_mode = "Black Hole"
        mode_toggle_field.set_value("Black Hole")
        orbs_field.label.text = "Orbs:"
        orbs_field.set_value(str(control_orb_amount))
        create_orbs(control_orb_amount)  # Recreate orbs for Black Hole mode
#

# Adjust the label of the sensitivity field based on the mode
def apply_sensitivity_setting():
    global SENSITIVITY_MULTIPLIER, WAVEFORM_SENSITIVITY, SPECTRUM_SENSITIVITY, sensitivity_field, visualization_mode
    try:
        if visualization_mode == "Black Hole":
            SENSITIVITY_MULTIPLIER = float(sensitivity_field.value)
            current_sensitivity = SENSITIVITY_MULTIPLIER
        elif visualization_mode == "Waveform":
            WAVEFORM_SENSITIVITY = float(sensitivity_field.value)
            current_sensitivity = WAVEFORM_SENSITIVITY
        elif visualization_mode == "Spectrum Bars":
            SPECTRUM_SENSITIVITY = float(sensitivity_field.value)
            current_sensitivity = SPECTRUM_SENSITIVITY
    except ValueError:
        pass
#

# Adjust the label of the sensitivity field based on the mode
def update_sensitivity_label():
    global sensitivity_field, visualization_mode
    if visualization_mode == "Black Hole":
        sensitivity_field.label.text = "Sensitivity (Orbs):"
        sensitivity_field.set_value(str(SENSITIVITY_MULTIPLIER))
    elif visualization_mode == "Waveform":
        sensitivity_field.label.text = "Sensitivity (Waveform):"
        sensitivity_field.set_value(str(WAVEFORM_SENSITIVITY))
    elif visualization_mode == "Spectrum Bars":
        sensitivity_field.label.text = "Sensitivity (Spectrum Bars):"
        sensitivity_field.set_value(str(SPECTRUM_SENSITIVITY))
#

# Ensure the waveform mode has proper handling:
def create_orbs_or_waveform_points(num):
    global orbs, control_waveform_points, control_spectrum_bars
    if visualization_mode == "Black Hole":
        orbs = []
        for i in range(num):
            orb = shapes.Circle(x=window.width // 2 + HORIZONTAL_ADJUSTMENT, y=window.height // 2, radius=18,
                                color=(255, 255, 255), batch=batch)
            orbs.append(orb)
    elif visualization_mode == "Waveform":
        control_waveform_points = num  # Store the waveform points value
        # Add logic here for drawing the waveform when in Waveform mode
        # For example, creating points or lines that will display the waveform
    elif visualization_mode == "Spectrum Bars":
        control_spectrum_bars = num  # Store the spectrum bars value
        # Add logic here for drawing the spectrum bars when in Spectrum Bars mode
#

def apply_hue_setting():
    global hue, control_hue, manual_hue
    try:
        control_hue = int(hue_field.value)
        if control_hue == 0:
            manual_hue = False
        else:
            hue = control_hue / 360.0
            manual_hue = True
    except ValueError:
        pass
#

def apply_speed_setting():
    global control_speed
    try:
        control_speed = min(float(speed_field.value), 0.9999999)  # Restrict speed value
    except ValueError:
        pass
#

def apply_gravity_setting():
    global control_gravity
    try:
        control_gravity = float(gravity_field.value)
    except ValueError:
        pass
#

def apply_orbs_setting():
    global control_orb_amount, control_waveform_points, control_spectrum_bars, orbs
    try:
        if visualization_mode == "Black Hole":
            control_orb_amount = int(orbs_field.value)
            create_orbs_or_waveform_points(control_orb_amount)
        elif visualization_mode == "Waveform":
            control_waveform_points = int(orbs_field.value)
            create_orbs_or_waveform_points(control_waveform_points)
        elif visualization_mode == "Spectrum Bars":
            control_spectrum_bars = int(orbs_field.value)
            create_orbs_or_waveform_points(control_spectrum_bars)
    except ValueError:
        pass
#

def apply_sensitivity_setting():
    global SENSITIVITY_MULTIPLIER, WAVEFORM_SENSITIVITY, SPECTRUM_SENSITIVITY, sensitivity_field, visualization_mode
    try:
        if visualization_mode == "Black Hole":
            SENSITIVITY_MULTIPLIER = float(sensitivity_field.value)
            current_sensitivity = SENSITIVITY_MULTIPLIER
        elif visualization_mode == "Waveform":
            WAVEFORM_SENSITIVITY = float(sensitivity_field.value)
            current_sensitivity = WAVEFORM_SENSITIVITY
        elif visualization_mode == "Spectrum Bars":
            SPECTRUM_SENSITIVITY = float(sensitivity_field.value)
            current_sensitivity = SPECTRUM_SENSITIVITY
    except ValueError:
        pass
#

def apply_brightness_floor_setting():
    global control_brightness_floor
    try:
        control_brightness_floor = float(brightness_floor_field.value) / 100.0  # Convert percentage to decimal
    except ValueError:
        pass
#

# Variable to track current decay rate
current_decay_rate = INITIAL_DECAY_RATE
last_decay_ramp_up_time = time.time()

def apply_decay():
    global current_gain_db_smoothed, current_decay_rate, last_decay_ramp_up_time

    # Increase decay rate over time if the value keeps dropping
    if time.time() - last_decay_ramp_up_time >= DECAY_RAMP_UP_INTERVAL:
        current_decay_rate = min(current_decay_rate + 1, MAX_DECAY_RATE)  # Ramp up the decay rate
        last_decay_ramp_up_time = time.time()

    # Apply decay
    current_gain_db_smoothed -= current_decay_rate
    if current_gain_db_smoothed < MIN_DB:
        current_gain_db_smoothed = MIN_DB
#

def draw_text():
    global glow_value, hue, control_brightness_floor, github_label

    try:
        brightness_percentage = max(glow_value * control_sensitivity, control_brightness_floor) * 100
        brightness_text = f"Brightness: {int(brightness_percentage)}%"

        r, g, b = colorsys.hsv_to_rgb(hue, 1, max(glow_value * control_sensitivity, control_brightness_floor))
        text_color = (int(r * 255), int(g * 255), int(b * 255), 255)

        label_brightness = pyglet.text.Label(
            brightness_text,
            font_size=BRIGHTNESS_FONT_SIZE,
            x=window.width // 2,
            y=window.height - 50,  # Adjust this for placement
            anchor_x='center',
            anchor_y='center',
            color=text_color
        )
        label_brightness.draw()

        # Draw GitHub label and store it globally
        github_label = pyglet.text.Label(
            "https://github.com/Fklyf/VisualBassSync",
            font_size=GITHUB_FONT_SIZE,
            x=10,
            y=10,
            anchor_x='left',
            anchor_y='bottom',
            color=(255, 255, 255, GITHUB_TRANSPARENCY)
        )
        github_label.draw()

    except Exception as e:
        logging.error(f"Error in draw_text: {e}")
#

def draw_control_menu():
    try:
        global control_hue, control_speed, control_gravity, control_orb_amount, control_sensitivity, control_brightness_floor, control_waveform_points, control_spectrum_bars
        global hue_field, speed_field, gravity_field, orbs_field, sensitivity_field, brightness_floor_field, mode_toggle_field

        align_control_menu()

        menu_x = window.width - MENU_WIDTH - MENU_PADDING
        menu_y = BOTTOM_MARGIN + MENU_HEIGHT + MENU_PADDING

        menu_background = shapes.Rectangle(x=menu_x - MENU_PADDING, y=menu_y - MENU_HEIGHT - MENU_PADDING,
                                           width=MENU_WIDTH + 2 * MENU_PADDING, height=MENU_HEIGHT + 2 * MENU_PADDING,
                                           color=(50, 50, 50), batch=batch)
        menu_background.opacity = 200
        menu_background.draw()

        mode_toggle_field.draw()
        hue_field.draw()
        speed_field.draw()
        gravity_field.draw()
        orbs_field.draw()
        sensitivity_field.draw()
        brightness_floor_field.draw()

    except Exception as e:
        logging.error(f"Error in draw_control_menu: {e}")
#

def align_control_menu():
    global hue_field, speed_field, gravity_field, orbs_field, sensitivity_field, brightness_floor_field, MENU_X, MENU_Y, mode_toggle_field

    MENU_X = window.width - MENU_WIDTH - MENU_PADDING
    MENU_Y = BOTTOM_MARGIN + MENU_HEIGHT + MENU_PADDING

    # Positioning each menu field based on row height
    mode_toggle_field.update_position(MENU_X + LABEL_X_OFFSET, MENU_Y - ROW_HEIGHT * 1)
    hue_field.update_position(MENU_X + LABEL_X_OFFSET, MENU_Y - ROW_HEIGHT * 2)
    speed_field.update_position(MENU_X + LABEL_X_OFFSET, MENU_Y - ROW_HEIGHT * 3)
    gravity_field.update_position(MENU_X + LABEL_X_OFFSET, MENU_Y - ROW_HEIGHT * 4)
    orbs_field.update_position(MENU_X + LABEL_X_OFFSET, MENU_Y - ROW_HEIGHT * 5)
    sensitivity_field.update_position(MENU_X + LABEL_X_OFFSET, MENU_Y - ROW_HEIGHT * 6)
    brightness_floor_field.update_position(MENU_X + LABEL_X_OFFSET, MENU_Y - ROW_HEIGHT * 7)
#

def smooth_brightness(current_brightness, target_brightness, update_interval):
    # Define a maximum change rate for brightness per second
    max_increase_rate = 0.1  # Reduce the increase rate for smoother brightness
    max_decrease_rate = 0.1  # Reduce the decrease rate for smoother brightness fall-off

    # Calculate allowed change rates based on the update interval
    allowed_increase = max_increase_rate * update_interval
    allowed_decrease = max_decrease_rate * update_interval

    # Smoothly adjust brightness towards target
    if target_brightness > current_brightness:
        return min(current_brightness + allowed_increase, target_brightness)
    elif target_brightness < current_brightness:
        return max(current_brightness - allowed_decrease, target_brightness)

    return current_brightness  # If brightness is stable, return it as is
#

def update(dt):
    global orbs, glow_value, hue, manual_hue, control_speed, control_gravity, control_brightness_floor

    try:
        if not manual_hue:
            hue += control_speed  # Use control speed for color cycling
            if hue > 1:
                hue -= 1

        # Adjust color brightness by multiplying glow_value with sensitivity
        r, g, b = colorsys.hsv_to_rgb(hue, 1, max(glow_value * control_sensitivity, control_brightness_floor))
        color = (int(r * 255), int(g * 255), int(b * 255))

        if visualization_mode == "Black Hole":
            for orb in orbs:
                distance_from_center = np.sqrt((orb.x - window.width // 2) ** 2 + (orb.y - window.height // 2) ** 2)
                if distance_from_center == 0:
                    distance_from_center = 1  # Prevent division by zero

                max_distance = min(window.width, window.height) // 2

                if ESCAPE_MODE:
                    orb.x += np.random.uniform(-SHAKE_INTENSITY, SHAKE_INTENSITY) * glow_value * control_sensitivity
                    orb.y += np.random.uniform(-SHAKE_INTENSITY, SHAKE_INTENSITY) * glow_value * control_sensitivity
                else:
                    direction_x = (window.width // 2 - orb.x) / distance_from_center
                    direction_y = (window.height // 2 - orb.y) / distance_from_center
                    orb.x += direction_x * (max_distance * (1 - glow_value)) + np.random.uniform(
                        -SHAKE_INTENSITY, SHAKE_INTENSITY) * glow_value * control_sensitivity
                    orb.y += direction_y * (max_distance * (1 - glow_value)) + np.random.uniform(
                        -SHAKE_INTENSITY, SHAKE_INTENSITY) * glow_value * control_sensitivity

                orb.x = max(orb.radius, min(window.width - orb.radius, orb.x))
                orb.y = max(orb.radius, min(window.height - orb.radius, orb.y))

                orb.radius = 10 + glow_value * 50 * control_sensitivity
                orb.opacity = int(glow_value * 255 * control_sensitivity)
                orb.color = color

    except Exception as e:
        logging.error(f"Error in update: {e}")
#

def draw_gain_bars(apply_smoothing=True):
    global glow_value, hue, current_gain_db, control_brightness_floor

    try:
        # Convert hue to RGB for bar color
        r, g, b = colorsys.hsv_to_rgb(hue, 1, max(glow_value, control_brightness_floor))
        color = (int(r * 255), int(g * 255), int(b * 255))

        # Define bar dimensions
        bar_width = int(50 * (window.width / 900))
        gap = int(150 * (window.width / 900))  # Adjust gap for correct positioning
        max_bar_height = window.height // 2  # Max height matching the center box

        # Clamp the gain_db value to ensure it does not visually go below -100 dB
        clamped_gain_db = max(current_gain_db, -100)

        # Optionally apply smoothing to the dB value
        if apply_smoothing:
            smoothed_gain_db = smooth_db_value(clamped_gain_db)
        else:
            smoothed_gain_db = clamped_gain_db

        # Calculate bar height based on the (smoothed) dB value
        left_bar_height = int(max((smoothed_gain_db + 100) / 100 * max_bar_height, 0))
        right_bar_height = left_bar_height

        # Position the bars on the screen
        left_bar_x = gap - bar_width  # Position to the left of the visual box
        right_bar_x = window.width - gap  # Position to the right of the visual box

        # Draw the left and right bars
        left_bar = shapes.Rectangle(x=left_bar_x, y=window.height // 2 - max_bar_height // 2, width=bar_width,
                                    height=left_bar_height, color=color, batch=batch)
        right_bar = shapes.Rectangle(x=right_bar_x, y=window.height // 2 - max_bar_height // 2, width=bar_width,
                                     height=right_bar_height, color=color, batch=batch)
        left_bar.draw()
        right_bar.draw()

        # Draw dB labels under the bars
        label_left_gain = pyglet.text.Label(f"{current_gain_db:.1f} dB", font_size=16,
                                            x=left_bar_x + bar_width // 2,
                                            y=window.height // 2 - max_bar_height // 2 - 30,
                                            anchor_x='center', anchor_y='center', color=(255, 255, 255, 255))
        label_right_gain = pyglet.text.Label(f"{current_gain_db:.1f} dB", font_size=16,
                                             x=right_bar_x + bar_width // 2,
                                             y=window.height // 2 - max_bar_height // 2 - 30,
                                             anchor_x='center', anchor_y='center', color=(255, 255, 255, 255))
        label_left_gain.draw()
        label_right_gain.draw()

    except Exception as e:
        logging.error(f"Error in draw_gain_bars: {e}")
#

# Smoothing function (adjust smoothing factor here if needed)
def smooth_db_value(new_db, smoothing_factor=0.1):  # Lower smoothing factor for faster response
    global current_gain_db
    current_gain_db = (smoothing_factor * current_gain_db) + ((1 - smoothing_factor) * new_db)
    return current_gain_db

# Initialize buffer for spectrum bars
spectrum_bar_buffers = [deque(maxlen=5) for _ in range(SPECTRUM_BARS)]  # Initialize with default bar count

def update_spectrum_bar_buffers():
    global spectrum_bar_buffers, control_spectrum_bars
    # Ensure the spectrum bar buffer is the right size for the current number of bars
    if len(spectrum_bar_buffers) != control_spectrum_bars:
        # Reinitialize the buffers to match the number of bars
        spectrum_bar_buffers = [deque(maxlen=5) for _ in range(control_spectrum_bars)]
#

def draw_spectrum_bars():
    global latest_audio_data, control_spectrum_bars, glow_value, hue, control_brightness_floor

    try:
        if latest_audio_data is None or len(latest_audio_data) < 2:
            return  # Not enough data to draw spectrum

        # Ensure control_spectrum_bars is even for proper mirroring
        if control_spectrum_bars % 2 != 0:
            control_spectrum_bars += 1  # Make it even

        # Ensure the buffers are updated to match the number of spectrum bars
        update_spectrum_bar_buffers()

        # Calculate FFT to get the frequency spectrum
        fft_data = np.abs(np.fft.fft(latest_audio_data))[:len(latest_audio_data) // 2]

        # Number of bins is half the total bars since we mirror them
        num_bins = control_spectrum_bars // 2

        # Ensure we have enough data to process
        if num_bins == 0 or len(fft_data) == 0:
            return

        # Calculate the size of each bin
        bin_size = len(fft_data) // num_bins

        # Compute the average amplitude for each bin
        bin_amplitudes = []
        for i in range(num_bins):
            start_index = i * bin_size
            end_index = start_index + bin_size if i < num_bins - 1 else len(fft_data)
            bin_amplitude = np.mean(fft_data[start_index:end_index])
            bin_amplitudes.append(bin_amplitude)

        # Mirror the bin amplitudes
        bar_amplitudes = bin_amplitudes[::-1] + bin_amplitudes

        # Apply smoothing to each bar using Exponential Moving Average (EMA)
        for i, amp in enumerate(bar_amplitudes):
            if i < len(spectrum_bar_buffers):
                if amp > 0:
                    spectrum_bar_buffers[i].append(amp)
                smoothed_amp = np.mean(spectrum_bar_buffers[i])  # Average over the buffer
                bar_amplitudes[i] = SPECTRUM_SMOOTHING_FACTOR * smoothed_amp + (1 - SPECTRUM_SMOOTHING_FACTOR) * bar_amplitudes[i]

        # Normalize amplitudes
        max_amplitude = max(bar_amplitudes)
        if max_amplitude > 0:
            bar_amplitudes = [amp / max_amplitude for amp in bar_amplitudes]

        # Calculate the scaling factors for middle emphasis and edge tapering
        middle_index = control_spectrum_bars // 2
        scaling_factors = [1.25 - abs(i - middle_index) / middle_index * 0.25 for i in range(control_spectrum_bars)]

        # Scale heights, applying the tapering effect
        bar_heights = [amp * scaling_factors[i] * (window.height // 2) * glow_value * control_sensitivity
                       for i, amp in enumerate(bar_amplitudes)]

        # Apply smoothing to glow_value
        smoothed_glow_value = smooth_brightness(glow_value, min(glow_value, 1.0), 1.0 / FPS_CAP)

        # Get color
        r, g, b = colorsys.hsv_to_rgb(hue, 1, max(smoothed_glow_value, control_brightness_floor))
        color = (int(r * 255), int(g * 255), int(b * 255))

        # Spacing settings
        spacing_fraction = 0.2  # Adjust as needed

        # Total number of spaces
        num_spaces = control_spectrum_bars - 1

        # Total units (bars + spacing units)
        total_units = control_spectrum_bars + spacing_fraction * num_spaces

        # Compute the base unit width
        unit_width = window.width / total_units

        # Bar width and spacing
        bar_width = unit_width  # Each bar occupies one unit
        spacing = unit_width * spacing_fraction

        # Total width of all bars and spaces
        total_bars_width = control_spectrum_bars * bar_width + num_spaces * spacing

        # Starting x position to center the bars
        starting_x = (window.width - total_bars_width) / 2

        # Draw bars with middle emphasis and taper effect
        for i in range(control_spectrum_bars):
            bar_x = starting_x + i * (bar_width + spacing)
            bar_height = bar_heights[i]
            bar_y = window.height // 2

            # Only draw bars with heights greater than a threshold to prevent drawing too small bars
            if bar_height > 1:
                bar = shapes.Rectangle(x=bar_x, y=bar_y - bar_height // 2, width=bar_width,
                                       height=bar_height, color=color)
                bar.draw()

    except Exception as e:
        logging.error(f"Error in draw_spectrum_bars: {e}")
#

# Initialize buffer for waveform data
waveform_buffers = [deque(maxlen=5) for _ in range(WAVEFORM_POINTS)]  # Initialize with default point count

def update_waveform_buffers():
    global waveform_buffers, control_waveform_points
    # Ensure the waveform buffer is the right size for the current number of points
    if len(waveform_buffers) != control_waveform_points:
        # Reinitialize the buffers to match the number of waveform points
        waveform_buffers = [deque(maxlen=5) for _ in range(control_waveform_points)]
#

def draw_waveform():
    global latest_audio_data, hue, control_brightness_floor, glow_value, control_sensitivity

    try:
        if latest_audio_data is None or len(latest_audio_data) < 2:
            return  # No audio data to process

        # Ensure the audio data has no NaN values
        latest_audio_data = np.nan_to_num(latest_audio_data, nan=0.0)

        # Downsample the waveform data to match the number of points (control_waveform_points)
        downsample_factor = max(1, len(latest_audio_data) // control_waveform_points)
        downsampled_waveform_data = latest_audio_data[::downsample_factor]

        # Ensure no NaN values in the downsampled data as well
        downsampled_waveform_data = np.nan_to_num(downsampled_waveform_data, nan=0.0)

        # Apply waveform smoothing with buffer
        for i in range(len(downsampled_waveform_data)):
            if i < len(waveform_buffers):
                if downsampled_waveform_data[i] > 0:
                    waveform_buffers[i].append(downsampled_waveform_data[i])
                smoothed_value = np.mean(waveform_buffers[i])  # Average over the buffer
                downsampled_waveform_data[i] = WAVEFORM_SMOOTHING_FACTOR * smoothed_value + (1 - WAVEFORM_SMOOTHING_FACTOR) * downsampled_waveform_data[i]

        # Convert hue to RGB for the waveform color
        r, g, b = colorsys.hsv_to_rgb(hue, 1, max(glow_value * control_sensitivity, control_brightness_floor))
        base_color = (int(r * 255), int(g * 255), int(b * 255))

        num_points = len(downsampled_waveform_data)
        if num_points < 2:
            return  # Not enough data to draw the waveform

        # Adjust x_step to fit the waveform across the screen width
        x_step = window.width / (num_points - 1)

        # Blending mode setup for a glow effect
        pyglet.gl.glEnable(pyglet.gl.GL_BLEND)
        pyglet.gl.glBlendFunc(pyglet.gl.GL_SRC_ALPHA, pyglet.gl.GL_ONE)

        if glow_value < 1.0:  # Normal pulsing behavior for glow values less than 100%
            # Define pulse intensity thresholds and corresponding widths
            thresholds = [0.15, 0.30, 0.45, 0.50, 0.60, 0.75, 0.85, 1.0]  # Intensity levels
            widths = [2, 2, 3, 3.5, 4, 5, 6, 7]  # Corresponding line widths

            # Calculate an offset for dynamic sliding effect
            time_offset = (time.time() * glow_value * 100) % window.width  # Adjust for sliding

            # Draw the waveform using line segments between consecutive points
            for i in range(num_points - 1):
                x1 = int(i * x_step)
                y1 = int(window.height // 2 + downsampled_waveform_data[i] * window.height // 2 * control_sensitivity)
                x2 = int((i + 1) * x_step)
                y2 = int(window.height // 2 + downsampled_waveform_data[i + 1] * window.height // 2 * control_sensitivity)

                # Add a pulsing glow effect to the waveform
                distance = abs((x1 + x2) / 2 - time_offset)
                distance_factor = min(1, distance / (window.width / 2))

                pulsed_color = (
                    int((1 - distance_factor) * base_color[0]),
                    int((1 - distance_factor) * base_color[1]),
                    int((1 - distance_factor) * base_color[2])
                )

                # Determine the pulse width based on glow_value thresholds
                pulse_width = widths[0]  # Default to minimum width
                for j, threshold in enumerate(thresholds):
                    if glow_value >= threshold:
                        pulse_width = widths[j]
                    else:
                        break  # Exit once the appropriate width is found

                # Draw the line with dynamic pulsing width and smoothing
                line = shapes.Line(x1, y1, x2, y2, width=pulse_width, color=pulsed_color, batch=batch)
                line.draw()

        else:  # Behavior for 100% brightness (glow_value == 1.0)
            # Draw a solid, glowing waveform at full brightness without pulsing or sliding
            for i in range(num_points - 1):
                x1 = int(i * x_step)
                y1 = int(window.height // 2 + downsampled_waveform_data[i] * window.height // 2 * control_sensitivity)
                x2 = int((i + 1) * x_step)
                y2 = int(window.height // 2 + downsampled_waveform_data[i + 1] * window.height // 2 * control_sensitivity)

                # Make the waveform color brighter at 100% brightness
                solid_color = (min(base_color[0] + 50, 255), min(base_color[1] + 50, 255), min(base_color[2] + 50, 255))

                # Draw the line without dynamic effects
                line = shapes.Line(x1, y1, x2, y2, width=5, color=solid_color, batch=batch)
                line.draw()

        # Disable blending after drawing
        pyglet.gl.glDisable(pyglet.gl.GL_BLEND)

    except Exception as e:
        logging.error(f"Error in draw_waveform: {e}")
#

def draw_separated_diamond(center_x, center_y, glow_value):
    # Adjust the separation distance based on brightness
    separation = glow_value * DIAMOND_POWER

    # Convert hue to RGB for the triangle colors
    r, g, b = colorsys.hsv_to_rgb(hue, 1, max(glow_value * control_sensitivity, control_brightness_floor))
    diamond_color = (int(r * 255), int(g * 255), int(b * 255))

    # 45-degree rotation matrix
    rotation_angle = math.radians(45)
    cos_angle = math.cos(rotation_angle)
    sin_angle = math.sin(rotation_angle)

    # Function to apply rotation to a point
    def rotate_point(x, y, cx, cy):
        # Translate point to origin
        x -= cx
        y -= cy
        # Apply rotation
        new_x = x * cos_angle - y * sin_angle
        new_y = x * sin_angle + y * cos_angle
        # Translate point back
        return new_x + cx, new_y + cy

    # Main triangle coordinates
    triangle_vertices = [
        # Top triangle
        [
            (center_x, center_y + separation),
            (center_x - DIAMOND_SIZE / 1, center_y + DIAMOND_SIZE + separation),
            (center_x + DIAMOND_SIZE / 1, center_y + DIAMOND_SIZE + separation)
        ],
        # Right triangle
        [
            (center_x + separation, center_y),
            (center_x + DIAMOND_SIZE + separation, center_y + DIAMOND_SIZE / 1),
            (center_x + DIAMOND_SIZE + separation, center_y - DIAMOND_SIZE / 1)
        ],
        # Bottom triangle
        [
            (center_x, center_y - separation),
            (center_x - DIAMOND_SIZE / 1, center_y - DIAMOND_SIZE - separation),
            (center_x + DIAMOND_SIZE / 1, center_y - DIAMOND_SIZE - separation)
        ],
        # Left triangle
        [
            (center_x - separation, center_y),
            (center_x - DIAMOND_SIZE - separation, center_y + DIAMOND_SIZE / 1),
            (center_x - DIAMOND_SIZE - separation, center_y - DIAMOND_SIZE / 1)
        ]
    ]

    # Apply rotation to the triangle vertices and draw them
    for triangle in triangle_vertices:
        rotated_triangle = [
            rotate_point(triangle[0][0], triangle[0][1], center_x, center_y),
            rotate_point(triangle[1][0], triangle[1][1], center_x, center_y),
            rotate_point(triangle[2][0], triangle[2][1], center_x, center_y)
        ]
        tri = shapes.Triangle(rotated_triangle[0][0], rotated_triangle[0][1],
                              rotated_triangle[1][0], rotated_triangle[1][1],
                              rotated_triangle[2][0], rotated_triangle[2][1],
                              color=diamond_color, batch=batch)
        tri.draw()

    # Draw smaller triangles if enabled
    if DRAW_SMALL_TRIANGLES:
        # First layer of smaller triangles
        small_triangle_1_vertices = [
            # Top small triangle
            [
                (center_x, center_y + separation + TRIANGLE_1_DISTANCE),
                (center_x - TRIANGLE_1_SIZE / 1, center_y + TRIANGLE_1_SIZE + separation + TRIANGLE_1_DISTANCE),
                (center_x + TRIANGLE_1_SIZE / 1, center_y + TRIANGLE_1_SIZE + separation + TRIANGLE_1_DISTANCE)
            ],
            # Right small triangle
            [
                (center_x + separation + TRIANGLE_1_DISTANCE, center_y),
                (center_x + TRIANGLE_1_SIZE + separation + TRIANGLE_1_DISTANCE, center_y + TRIANGLE_1_SIZE / 1),
                (center_x + TRIANGLE_1_SIZE + separation + TRIANGLE_1_DISTANCE, center_y - TRIANGLE_1_SIZE / 1)
            ],
            # Bottom small triangle
            [
                (center_x, center_y - separation - TRIANGLE_1_DISTANCE),
                (center_x - TRIANGLE_1_SIZE / 1, center_y - TRIANGLE_1_SIZE - separation - TRIANGLE_1_DISTANCE),
                (center_x + TRIANGLE_1_SIZE / 1, center_y - TRIANGLE_1_SIZE - separation - TRIANGLE_1_DISTANCE)
            ],
            # Left small triangle
            [
                (center_x - separation - TRIANGLE_1_DISTANCE, center_y),
                (center_x - TRIANGLE_1_SIZE - separation - TRIANGLE_1_DISTANCE, center_y + TRIANGLE_1_SIZE / 1),
                (center_x - TRIANGLE_1_SIZE - separation - TRIANGLE_1_DISTANCE, center_y - TRIANGLE_1_SIZE / 1)
            ]
        ]

        # Apply rotation and draw smaller triangles for the first layer
        for small_triangle in small_triangle_1_vertices:
            rotated_small_triangle = [
                rotate_point(small_triangle[0][0], small_triangle[0][1], center_x, center_y),
                rotate_point(small_triangle[1][0], small_triangle[1][1], center_x, center_y),
                rotate_point(small_triangle[2][0], small_triangle[2][1], center_x, center_y)
            ]
            tri = shapes.Triangle(rotated_small_triangle[0][0], rotated_small_triangle[0][1],
                                  rotated_small_triangle[1][0], rotated_small_triangle[1][1],
                                  rotated_small_triangle[2][0], rotated_small_triangle[2][1],
                                  color=diamond_color, batch=batch)
            tri.draw()

        # Second layer of smaller triangles (behind the first)
        small_triangle_2_vertices = [
            # Top small triangle
            [
                (center_x, center_y + separation + TRIANGLE_1_DISTANCE + TRIANGLE_2_DISTANCE),
                (center_x - TRIANGLE_2_SIZE / 1, center_y + TRIANGLE_2_SIZE + separation + TRIANGLE_1_DISTANCE + TRIANGLE_2_DISTANCE),
                (center_x + TRIANGLE_2_SIZE / 1, center_y + TRIANGLE_2_SIZE + separation + TRIANGLE_1_DISTANCE + TRIANGLE_2_DISTANCE)
            ],
            # Right small triangle
            [
                (center_x + separation + TRIANGLE_1_DISTANCE + TRIANGLE_2_DISTANCE, center_y),
                (center_x + TRIANGLE_2_SIZE + separation + TRIANGLE_1_DISTANCE + TRIANGLE_2_DISTANCE, center_y + TRIANGLE_2_SIZE / 1),
                (center_x + TRIANGLE_2_SIZE + separation + TRIANGLE_1_DISTANCE + TRIANGLE_2_DISTANCE, center_y - TRIANGLE_2_SIZE / 1)
            ],
            # Bottom small triangle
            [
                (center_x, center_y - separation - TRIANGLE_1_DISTANCE - TRIANGLE_2_DISTANCE),
                (center_x - TRIANGLE_2_SIZE / 1, center_y - TRIANGLE_2_SIZE - separation - TRIANGLE_1_DISTANCE - TRIANGLE_2_DISTANCE),
                (center_x + TRIANGLE_2_SIZE / 1, center_y - TRIANGLE_2_SIZE - separation - TRIANGLE_1_DISTANCE - TRIANGLE_2_DISTANCE)
            ],
            # Left small triangle
            [
                (center_x - separation - TRIANGLE_1_DISTANCE - TRIANGLE_2_DISTANCE, center_y),
                (center_x - TRIANGLE_2_SIZE - separation - TRIANGLE_1_DISTANCE - TRIANGLE_2_DISTANCE, center_y + TRIANGLE_2_SIZE / 1),
                (center_x - TRIANGLE_2_SIZE - separation - TRIANGLE_1_DISTANCE - TRIANGLE_2_DISTANCE, center_y - TRIANGLE_2_SIZE / 1)
            ]
        ]

        # Apply rotation and draw second layer of smaller triangles
        for small_triangle in small_triangle_2_vertices:
            rotated_small_triangle = [
                rotate_point(small_triangle[0][0], small_triangle[0][1], center_x, center_y),
                rotate_point(small_triangle[1][0], small_triangle[1][1], center_x, center_y),
                rotate_point(small_triangle[2][0], small_triangle[2][1], center_x, center_y)
            ]
            tri = shapes.Triangle(rotated_small_triangle[0][0], rotated_small_triangle[0][1],
                                  rotated_small_triangle[1][0], rotated_small_triangle[1][1],
                                  rotated_small_triangle[2][0], rotated_small_triangle[2][1],
                                  color=diamond_color, batch=batch)
            tri.draw()

        # Third layer of smaller triangles (behind the second)
        small_triangle_3_vertices = [
            # Top small triangle
            [
                (center_x, center_y + separation + TRIANGLE_1_DISTANCE + TRIANGLE_2_DISTANCE + TRIANGLE_3_DISTANCE),
                (center_x - TRIANGLE_3_SIZE / 1, center_y + TRIANGLE_3_SIZE + separation + TRIANGLE_1_DISTANCE + TRIANGLE_2_DISTANCE + TRIANGLE_3_DISTANCE),
                (center_x + TRIANGLE_3_SIZE / 1, center_y + TRIANGLE_3_SIZE + separation + TRIANGLE_1_DISTANCE + TRIANGLE_2_DISTANCE + TRIANGLE_3_DISTANCE)
            ],
            # Right small triangle
            [
                (center_x + separation + TRIANGLE_1_DISTANCE + TRIANGLE_2_DISTANCE + TRIANGLE_3_DISTANCE, center_y),
                (center_x + TRIANGLE_3_SIZE + separation + TRIANGLE_1_DISTANCE + TRIANGLE_2_DISTANCE + TRIANGLE_3_DISTANCE, center_y + TRIANGLE_3_SIZE / 1),
                (center_x + TRIANGLE_3_SIZE + separation + TRIANGLE_1_DISTANCE + TRIANGLE_2_DISTANCE + TRIANGLE_3_DISTANCE, center_y - TRIANGLE_3_SIZE / 1)
            ],
            # Bottom small triangle
            [
                (center_x, center_y - separation - TRIANGLE_1_DISTANCE - TRIANGLE_2_DISTANCE - TRIANGLE_3_DISTANCE),
                (center_x - TRIANGLE_3_SIZE / 1, center_y - TRIANGLE_3_SIZE - separation - TRIANGLE_1_DISTANCE - TRIANGLE_2_DISTANCE - TRIANGLE_3_DISTANCE),
                (center_x + TRIANGLE_3_SIZE / 1, center_y - TRIANGLE_3_SIZE - separation - TRIANGLE_1_DISTANCE - TRIANGLE_2_DISTANCE - TRIANGLE_3_DISTANCE)
            ],
            # Left small triangle
            [
                (center_x - separation - TRIANGLE_1_DISTANCE - TRIANGLE_2_DISTANCE - TRIANGLE_3_DISTANCE, center_y),
                (center_x - TRIANGLE_3_SIZE - separation - TRIANGLE_1_DISTANCE - TRIANGLE_2_DISTANCE - TRIANGLE_3_DISTANCE, center_y + TRIANGLE_3_SIZE / 1),
                (center_x - TRIANGLE_3_SIZE - separation - TRIANGLE_1_DISTANCE - TRIANGLE_2_DISTANCE - TRIANGLE_3_DISTANCE, center_y - TRIANGLE_3_SIZE / 1)
            ]
        ]

        # Apply rotation and draw third layer of smaller triangles
        for small_triangle in small_triangle_3_vertices:
            rotated_small_triangle = [
                rotate_point(small_triangle[0][0], small_triangle[0][1], center_x, center_y),
                rotate_point(small_triangle[1][0], small_triangle[1][1], center_x, center_y),
                rotate_point(small_triangle[2][0], small_triangle[2][1], center_x, center_y)
            ]
            tri = shapes.Triangle(rotated_small_triangle[0][0], rotated_small_triangle[0][1],
                                  rotated_small_triangle[1][0], rotated_small_triangle[1][1],
                                  rotated_small_triangle[2][0], rotated_small_triangle[2][1],
                                  color=diamond_color, batch=batch)
            tri.draw()
#

def draw_circle_outline(center_x, center_y, radius, outline_thickness, outline_color, batch):
    # Generate points for the polygonal circle outline
    points = []
    angle_step = 2 * math.pi / NUM_SIDES

    # Calculate vertices for the outer radius
    for i in range(NUM_SIDES):
        angle = i * angle_step
        x = center_x + radius * math.cos(angle)
        y = center_y + radius * math.sin(angle)
        points.append((x, y))

    # Draw the outline as a single polygon with thickness
    for i in range(NUM_SIDES):
        next_index = (i + 1) % NUM_SIDES
        # Draw thicker lines to simulate outline thickness (instead of concentric circles)
        shapes.Line(points[i][0], points[i][1],
                    points[next_index][0], points[next_index][1],
                    width=outline_thickness, color=outline_color, batch=batch).draw()
#

def draw_radial_db_meters():
    global latest_audio_data, glow_value, hue, control_sensitivity, control_brightness_floor

    try:
        if latest_audio_data is None or len(latest_audio_data) < 2:
            return  # Not enough data to draw spectrum

        # Use the FFT to get frequency spectrum data (similar to spectrum bars)
        fft_data = np.abs(np.fft.fft(latest_audio_data))[:len(latest_audio_data) // 2]

        # Use constants for the number of bars, bar width, etc.
        num_bars = DEFAULT_NUM_BARS
        bar_width = DEFAULT_BAR_WIDTH
        max_bar_length = DEFAULT_MAX_BAR_LENGTH  # Limit the length of the bars
        base_radius = DEFAULT_RADIUS  # Base radius for the bars

        # Normalize FFT data and apply sensitivity scaling
        max_amplitude = np.max(fft_data) if np.max(fft_data) != 0 else 1
        bar_amplitudes = [amp / max_amplitude for amp in fft_data[:num_bars]]

        # Convert hue to RGB for bar colors
        r, g, b = colorsys.hsv_to_rgb(hue, 1, max(glow_value * control_sensitivity, control_brightness_floor))
        color = (int(r * 255), int(g * 255), int(b * 255))

        # Add dynamic radius effect (bouncing based on brightness/glow value)
        dynamic_radius = base_radius + glow_value * BOUNCE_INTENSITY

        # Adjust the bar length based on glow value to create the "bouncing" effect
        dynamic_bar_length = max_bar_length + glow_value * BOUNCE_INTENSITY

        # Draw the circular outline first (so it appears under the dB meters)
        center_x = window.width // 2
        center_y = window.height // 2
        circle_radius = INNER_CIRCLE_RADIUS + glow_value * BOUNCE_INTENSITY  # Adjust radius with glow value

        # Calculate the outline color using hue and glow_value
        outline_color_r, outline_color_g, outline_color_b = colorsys.hsv_to_rgb(hue, 1, max(glow_value * control_sensitivity, control_brightness_floor))
        circle_outline_color = (int(outline_color_r * 255), int(outline_color_g * 255), int(outline_color_b * 255))

        # Draw the circular outline using the optimized single polygon with thickness
        draw_circle_outline(center_x, center_y, circle_radius, OUTLINE_THICKNESS, circle_outline_color, batch)

        # Now draw the bars radially in a circle
        for i in range(num_bars):
            # Calculate the angle for the current bar
            angle = np.radians(i * ANGLE_INCREMENT)

            # Calculate the dB value for each bar and set the size to 0 if below -50 dB
            amplitude = bar_amplitudes[i] * max_amplitude
            db_value = 20 * np.log10(amplitude) if amplitude > 0 else -100  # Convert amplitude to dB
            if db_value < -50:
                bar_length = 0  # Set bar length to 0 if dB is below -50
            else:
                bar_length = bar_amplitudes[i] * dynamic_bar_length  # Normal bar length otherwise

            # Calculate the start and end positions of the bar with dynamic radius and length
            start_x = int(center_x + dynamic_radius * np.cos(angle))
            start_y = int(center_y + dynamic_radius * np.sin(angle))
            end_x = int(start_x + bar_length * np.cos(angle))
            end_y = int(start_y + bar_length * np.sin(angle))

            # Draw the bar (as a line or a narrow rectangle)
            line = shapes.Line(start_x, start_y, end_x, end_y, width=bar_width, color=color, batch=batch)
            line.draw()

        # Draw the separated triangles (without stretching)
        draw_separated_diamond(center_x, center_y, glow_value)  # Call the function to draw the separated triangles

    except Exception as e:
        logging.error(f"Error in draw_radial_db_meters: {e}")
#

# Global angle for rotation (used in Pygame)
angle = 5

pygame.init() # Initialize Pygame
pygame_surface = None  # Declare the surface as None initially
pygame_texture = None  # Declare the texture as None initially

# Global state and constants
cube_vertices = []  # Stores the vertices of the cube
cube_trail_history = []  # Stores past frames for trail effects
DEFAULT_SCALE_FACTOR = 100
MAX_SCALE_FACTOR = 6.0

# Toggle for enabling/disabling trails
ENABLE_BOX_IN_BOX = False # Toggle for the "box-in-box" effect
ENABLE_TRAILS = True  # Toggle for the trail effect
ALPHA_CONSTANT = 157.50
NUM_BOXES = 9 # Number of frames to retain for trail effect
TRAIL_FADE_FACTORS = [0.9, 0.40, 0.35, 0.30, 0.25, 0.20, 0.15, 0.10, 0.05]  # Fade factors for trails

# Initialize screen dimensions
SCREEN_WIDTH = 800
SCREEN_HEIGHT = 600

def draw_pygame_to_pyglet(pyglet_window_width, pyglet_window_height):
    """Draw the Pygame surface stretched to fit the entire Pyglet window."""
    global pygame_texture

    # Resize the Pygame surface to the Pyglet window dimensions
    scaled_surface = pygame.transform.scale(pygame_surface, (pyglet_window_width, pyglet_window_height))

    # Get the Pygame surface as an image
    pygame_image = pygame.image.tostring(scaled_surface, "RGBA", False)

    # Create a Pyglet image from the Pygame surface
    pyglet_image_data = pyglet.image.ImageData(pyglet_window_width,
                                               pyglet_window_height,
                                               'RGBA',
                                               pygame_image)

    # Draw the Pyglet image data on the screen, covering the full window
    pyglet_image_data.blit(0, 0)

def init_cube():
    """Initialize the cube vertices."""
    global cube_vertices
    cube_vertices = [
        np.matrix([-1, -1, 1]),  # Front-bottom-left
        np.matrix([1, -1, 1]),   # Front-bottom-right
        np.matrix([1, 1, 1]),    # Front-top-right
        np.matrix([-1, 1, 1]),   # Front-top-left
        np.matrix([-1, -1, -1]), # Back-bottom-left
        np.matrix([1, -1, -1]),  # Back-bottom-right
        np.matrix([1, 1, -1]),   # Back-top-right
        np.matrix([-1, 1, -1])   # Back-top-left
    ]

# Ensure this is called whenever the window size changes
def pygame_window_resize(window_width, window_height):
    update_pygame_surface(window_width, window_height)

def update_pygame_surface(window_width, window_height):
    global pygame_surface, pygame_texture
    # Dynamically resize the Pygame surface based on the current window size
    pygame_surface = pygame.Surface((window_width, window_height))
    # Update the Pyglet texture based on the resized surface
    pygame_texture = pyglet.image.Texture.create(window_width, window_height)

    # After resizing the surface, we must update the screen dimensions globally
    global SCREEN_WIDTH, SCREEN_HEIGHT
    SCREEN_WIDTH = window_width * 2 + 2
    SCREEN_HEIGHT = window_height * 2 + 2

def draw_polygon_mode(screen, glow_value, hue, screen_width, screen_height):
    """Render the rotating cube, scaling and centering it based on glow_value and hue."""
    global cube_trail_history

    if not cube_vertices:
        init_cube()

    # Convert hue to RGB for line color
    r, g, b = colorsys.hsv_to_rgb(hue, 1, max(glow_value * control_sensitivity, control_brightness_floor))
    line_color = (int(r * 255), int(g * 255), int(b * 255))

    # Calculate scaling factor based on glow_value and screen dimensions
    min_dimension = min(screen_width, screen_height)  # Maintain aspect ratio
    scale = (DEFAULT_SCALE_FACTOR * (control_brightness_floor + (glow_value * MAX_SCALE_FACTOR))) * (min_dimension / 800)

    # Define the center of the screen (for proper centering)
    center_x, center_y = screen_width // 2, screen_height // 2

    # Current rotation angle (time-based)
    angle = pygame.time.get_ticks() * 0.0010

    # Define rotation matrices (Z, Y, X)
    rotation_z = np.matrix([
        [math.cos(angle), -math.sin(angle), 0],
        [math.sin(angle), math.cos(angle), 0],
        [0, 0, 1]
    ])
    rotation_y = np.matrix([
        [math.cos(angle), 0, math.sin(angle)],
        [0, 1, 0],
        [-math.sin(angle), 0, math.cos(angle)]
    ])
    rotation_x = np.matrix([
        [1, 0, 0],
        [0, math.cos(angle), -math.sin(angle)],
        [0, math.sin(angle), math.cos(angle)]
    ])

    ### TRAIL Effect Handling (if enabled) ###
    if ENABLE_TRAILS:
        # Clear the screen slightly with a translucent black surface to create a fading effect
        fade_surface = pygame.Surface((screen_width, screen_height), pygame.SRCALPHA)
        fade_surface.set_alpha(ALPHA_CONSTANT)  # Adjust the alpha for more or less fading
        fade_surface.fill((0, 0, 0))  # Transparent black
        screen.blit(fade_surface, (0, 0))

    else:
        # If trails are disabled, clear the screen before drawing (prevents drawing on top of old frames)
        screen.fill((0, 0, 0))  # Clear screen to black

    ### BOX-IN-BOX Effect Handling (if enabled) ###
    if ENABLE_BOX_IN_BOX:
        # Store the current frame data for the box-in-box trail
        current_frame_data = {
            'scale': scale,
            'line_color': line_color,
            'rotation_x': rotation_x,
            'rotation_y': rotation_y,
            'rotation_z': rotation_z,
        }

        # Add the current frame to trail history and limit the size
        cube_trail_history.append(current_frame_data)
        if len(cube_trail_history) > NUM_BOXES:
            cube_trail_history.pop(0)

        # Draw all past frames (box-in-box effect)
        for i, trail_data in enumerate(cube_trail_history):
            trail_brightness = TRAIL_FADE_FACTORS[i % len(TRAIL_FADE_FACTORS)]  # Cycle through fade factors
            trail_color = tuple(int(c * trail_brightness) for c in trail_data['line_color'])
            trail_scale = trail_data['scale'] * trail_brightness  # Scale trails down
            draw_cube(screen, center_x, center_y, trail_data['rotation_x'], trail_data['rotation_y'],
                      trail_data['rotation_z'], trail_scale, trail_color)

    # Draw the cube with correct arguments
    draw_cube(screen, center_x, center_y, rotation_x, rotation_y, rotation_z, scale, line_color)

def draw_cube(screen, center_x, center_y, rotation_x, rotation_y, rotation_z, scale, line_color):
    """Helper function to draw the 3D cube and ensure it is centered."""

    # Projection matrix for projecting 3D points into 2D
    projection_matrix = np.matrix([
        [1, 0, 0],
        [0, 1, 0]
    ])

    projected_points = []

    # Rotate and project each 3D point onto 2D
    for point in cube_vertices:
        # Apply the rotations on the cube vertices
        rotated_point = np.dot(rotation_z, point.reshape((3, 1)))  # Rotate around Z
        rotated_point = np.dot(rotation_y, rotated_point)  # Rotate around Y
        rotated_point = np.dot(rotation_x, rotated_point)  # Rotate around X

        # Depth-based scaling, adjust Z for perspective (modify the 3 as necessary)
        z = rotated_point[2].item() + 5  # You might want to increase this from 3 to 5 or more

        if z == 0:
            z = 0.1  # Prevent divide by zero errors

        # Adjust the scale based on depth (perspective scaling)
        perspective_scale = scale / z  # Scaling the object based on depth

        # Project the 3D point into 2D space using the projection matrix
        projected_2d = np.dot(projection_matrix, rotated_point)

        # Calculate the x and y coordinates with perspective and centering
        x = int(projected_2d[0].item() * perspective_scale) + center_x
        y = int(projected_2d[1].item() * perspective_scale) + center_y

        # Append the projected point to the list of 2D coordinates
        projected_points.append([x, y])

        # Draw each vertex (optional to make invisible if you want)
        pygame.draw.circle(screen, line_color, (x, y), 5)

    # Helper function to connect projected points and draw lines
    def connect_points(i, j):
        pygame.draw.line(screen, line_color,
                         (projected_points[i][0], projected_points[i][1]),
                         (projected_points[j][0], projected_points[j][1]), 2)

    # Connect the points to form the cube's edges
    for p in range(4):
        connect_points(p, (p + 1) % 4)  # Connect front face
        connect_points(p + 4, ((p + 1) % 4) + 4)  # Connect back face
        connect_points(p, p + 4)  # Connect front and back faces

def pygame_visualizer(window_width, window_height):
    """Render the Pygame polygon to an off-screen surface."""
    update_pygame_surface(window_width, window_height)  # Ensure the surface is correctly sized
    screen_width, screen_height = pygame_surface.get_width(), pygame_surface.get_height()
    draw_polygon_mode(pygame_surface, glow_value, hue, screen_width, screen_height)
    return pygame_surface

def update_visualization_with_audio(new_brightness_value, window_width, window_height):
    """Update the visualizer based on the new audio-driven brightness value."""
    global brightness
    brightness = new_brightness_value
    surface = pygame_visualizer(window_width, window_height)  # Get updated screen surface
    return surface

#
def toggle_control_menu():
        global control_menu_visible, hue_field, speed_field, gravity_field, orbs_field, sensitivity_field, brightness_floor_field, mode_toggle_field
        control_menu_visible = not control_menu_visible

        if not control_menu_visible:
            mode_toggle_field.set_active(False)
            hue_field.set_active(False)
            speed_field.set_active(False)
            gravity_field.set_active(False)
            orbs_field.set_active(False)
            sensitivity_field.set_active(False)
            brightness_floor_field.set_active(False)
#

def process_control_menu_click(x, y):
        global hue_field, speed_field, gravity_field, orbs_field, sensitivity_field, brightness_floor_field

        # Deactivate all fields
        hue_field.set_active(False)
        speed_field.set_active(False)
        gravity_field.set_active(False)
        orbs_field.set_active(False)
        sensitivity_field.set_active(False)
        brightness_floor_field.set_active(False)

        # Activate the clicked field
        if hue_field.hit_test(x, y):
            hue_field.set_active(True)
        elif speed_field.hit_test(x, y):
            speed_field.set_active(True)
        elif gravity_field.hit_test(x, y):
            gravity_field.set_active(True)
        elif orbs_field.hit_test(x, y):
            orbs_field.set_active(True)
        elif sensitivity_field.hit_test(x, y):
            sensitivity_field.set_active(True)
        elif brightness_floor_field.hit_test(x, y):
            brightness_floor_field.set_active(True)
#

def apply_control_settings():
        global hue, control_hue, control_speed, control_gravity, control_orb_amount, control_sensitivity, control_brightness_floor, manual_hue, control_waveform_points, control_spectrum_bars

        try:
            control_hue = int(hue_field.value)
            if control_hue == 0:
                manual_hue = False
            else:
                hue = control_hue / 360.0
                manual_hue = True

            control_speed = min(float(speed_field.value), 0.9999999)  # Restrict speed value
            control_gravity = float(gravity_field.value)
            control_sensitivity = float(sensitivity_field.value)
            control_brightness_floor = float(brightness_floor_field.value) / 100.0  # Convert percentage to decimal

            if visualization_mode == "Black Hole":
                control_orb_amount = int(orbs_field.value)
                create_orbs(control_orb_amount)  # Update orbs based on new control values
            elif visualization_mode == "Waveform":
                control_waveform_points = int(orbs_field.value)
                # Waveform-specific updates could go here if needed
            elif visualization_mode == "Spectrum Bars":
                control_spectrum_bars = int(orbs_field.value)
                # Spectrum Bars-specific updates could go here if needed

        except ValueError:
            pass
#

def set_default_mode():
    global manual_hue, control_hue, control_speed, control_gravity, control_orb_amount, control_sensitivity, control_brightness_floor, control_waveform_points, control_spectrum_bars
    manual_hue = False
    control_hue = 0
    control_speed = 0.0004
    control_gravity = BLACK_HOLE_STRENGTH
    control_orb_amount = NUM_ORBS
    control_waveform_points = WAVEFORM_POINTS
    control_spectrum_bars = SPECTRUM_BARS
    control_sensitivity = SENSITIVITY_MULTIPLIER
    control_brightness_floor = 0.0
    create_orbs_or_waveform_points(control_orb_amount)

    pyglet.clock.schedule_interval(update, 1 / 240.0)
#

def select_device():
    try:
        # Query available audio devices
        devices = sd.query_devices()
        input_devices = [(i, device['name']) for i, device in enumerate(devices) if device['max_input_channels'] > 0]

        # Check if running on macOS
        if platform.system() == "Darwin":
            print("Available Input Devices:")
            for index, name in input_devices:
                print(f"{index}: {name}")

            # Use command-line selection instead of Tkinter for macOS
            selected_device_index = int(input("Enter the index of the input device: "))
            if 0 <= selected_device_index < len(input_devices):
                print(f"Using input device: {input_devices[selected_device_index][1]}")
                run_visualizer(selected_device_index)  # Start the visualizer
            else:
                print(f"Invalid index. Please enter a number between 0 and {len(input_devices)-1}.")
                sys.exit(1)

        else:
            # Non-macOS systems: Use Tkinter for device selection
            device_selection_window = tk.Tk()
            device_selection_window.title("Select Input Device")

            # Set the window to be always on top
            device_selection_window.attributes("-topmost", True)

            label = tk.Label(device_selection_window, text="Select the input device index for capturing system audio:")
            label.pack(pady=10)

            # Dropdown for selecting the input device
            device_combo = ttk.Combobox(device_selection_window,
                                        values=[f"{index}: {name}" for index, name in input_devices], width=50)
            device_combo.pack(pady=10)
            device_combo.current(0)  # Set default selection

            def on_select():
                selected_device_index = int(device_combo.get().split(':')[0])
                device_selection_window.destroy()  # Close the selection window
                run_visualizer(selected_device_index)  # Start visualizer after selection window closes

            # Button to confirm selection
            select_button = tk.Button(device_selection_window, text="Select", command=on_select)
            select_button.pack(pady=20)

            # Run the Tkinter main loop (this will block further execution until window is closed)
            device_selection_window.mainloop()

    except Exception as e:
        logging.error(f"Failed to select device: {e}")
        sys.exit(1)


#


#

def run_visualizer(selected_device_index):
    print(f"Using input device: {selected_device_index}")
    global hue, hue_field, speed_field, gravity_field, orbs_field, sensitivity_field, brightness_floor_field, mode_toggle_field
    global center_x, center_y  # Declare global for the center coordinates

    try:
        # Initialize the Pygame surface with current window dimensions
        window_width = SCREEN_WIDTH  # Use initial width; it can be updated dynamically
        window_height = SCREEN_HEIGHT

        # Initialize the Pygame surface and texture dynamically based on the window size
        update_pygame_surface(window_width, window_height)

        # Initialize editable fields after selecting device
        mode_toggle_field = EditableField("Mode:", MENU_X + LABEL_X_OFFSET, MENU_Y - ROW_HEIGHT * 1,
                                          initial_value="Black Hole")
        hue_field = EditableField("Hue (1-360):", MENU_X + LABEL_X_OFFSET, MENU_Y - ROW_HEIGHT * 2,
                                  initial_value=str(control_hue))
        speed_field = EditableField("Speed:", MENU_X + LABEL_X_OFFSET, MENU_Y - ROW_HEIGHT * 3,
                                    initial_value=str(control_speed))
        gravity_field = EditableField("Gravity:", MENU_X + LABEL_X_OFFSET, MENU_Y - ROW_HEIGHT * 4,
                                      initial_value=str(control_gravity))
        orbs_field = EditableField("Orbs:", MENU_X + LABEL_X_OFFSET, MENU_Y - ROW_HEIGHT * 5,
                                   initial_value=str(control_orb_amount))
        sensitivity_field = EditableField("Sensitivity:", MENU_X + LABEL_X_OFFSET, MENU_Y - ROW_HEIGHT * 6,
                                          initial_value=str(control_sensitivity))
        brightness_floor_field = EditableField("Brightness Floor:", MENU_X + LABEL_X_OFFSET,
                                               MENU_Y - ROW_HEIGHT * 7,
                                               initial_value=str(int(control_brightness_floor * 100)))

        hue = 0  # Initialize hue for color cycling
        create_orbs(control_orb_amount)  # Create orbs based on current control value
        start_audio_stream(selected_device_index)  # Start the audio stream
        pyglet.clock.schedule_interval(update, 1 / 240.0)  # Update 240 times per second
        pyglet.app.run()  # Run the visualizer only after device selection
    except Exception as e:
        logging.error(f"Error in run_visualizer: {e}")
        sys.exit(1)

#

def cleanup():
    try:
        pyglet.app.exit()
        if stream is not None:
            stream.close()
    except Exception as e:
        logging.error(f"Error during cleanup: {e}")
atexit.register(cleanup)
#

if __name__ == "__main__":
    select_device()
