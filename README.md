# ADS-B Transit Predictor

![Logo](assets/icon.png)

A real-time visualization tool for predicting aircraft transits across the sun and moon, and close encounters, using live ADS-B data.

---

## Motivation

As an aviation enthusiast and photographer, I was fascinated by two distinct and technically demanding photographic challenges: capturing the rare moment two aircraft appear to have a close encounter, and capturing the dramatic transit of a single aircraft across the sun or moon. Both types of events are incredibly fleeting, lasting only seconds, and their visibility is entirely dependent on the observer's precise location and timing. I realized that a purely observational approach was not just inefficient, but fundamentally limited by chance. This project was born out of a desire to create a scientific tool to solve this problem—to move from serendipity to predictable, planned photographic opportunities. The software achieves this by fusing real-time aeronautical data (ADS-B) with predictive geometry and celestial mechanics.

## Key Features

*   **Real-time Flight Tracking**: Establishes a direct connection to a local dump1090 ADS-B decoder, rendering live aircraft positions, altitude, speed, and heading on a dynamic map display.
*   **Transit Prediction**: For any detected aircraft, the software calculates and can visualizes its future ground shadow track across the Sun and Moon. This "transit corridor" shows an observer exactly where to be on the ground to witness the event.
*   **Predictive Encounter Alerts**: Leverages flight path extrapolation to alert the user to potential close angular separations between two aircraft from the observer's unique vantage point.
*   **Geospatial Context**: Integrates a multi-layered map with foundational vector data from **Natural Earth** (coastlines, borders) and a comprehensive aeronautical database from the **OurAirports** project, including thousands of airports, runways, and navaids.
*   **Integrated ADS-B Receiver**: The Windows release package comes bundled with a pre-compiled version of **dump1090**, providing an "out-of-the-box" experience for users with an RTL-SDR dongle.

---

## Technical Stack

This application was built using a combination of powerful Python libraries and standard scientific models to handle everything from data processing to visualization and celestial calculations:

*   **Core Logic**: Python 3
*   **Real-time Rendering & UI**: Pygame for the main map display and event loop.
*   **Configuration & Dialogs**: Tkinter / ttk for creating the user-friendly configuration menus.
*   **Celestial Mechanics**: Skyfield for high-precision astronomical calculations, utilizing the **JPL DE421 ephemeris**.
*   **Numerical Computing**: NumPy for efficient vector and matrix operations in positional predictions.
*   **Geospatial Analysis**: Shapely and PyShp for processing vector map data, with all geodetic calculations based on the **WGS84 ellipsoid model**.
*   **Networking**: Python's built-in `socket` library for streaming data from dump1090.

---

## Screenshots

![Main application interface](assets/screenshot_1.png)
*<p align="center">The main interface showing live aircraft, transit corridors, and predicted events.</p>*

![Configuration menu](assets/screenshot_2.png)
*<p align="center">The configuration menu, allowing for customization of user location, prediction parameters, and map layers.</p>*

![Example of a close encounter](assets/eg.jpg)
*<p align="center">A screenshot displaying two four-engine jets in close proximity.</p>*

---

## Getting Started

### For End Users (Windows)

1.  Navigate to the project's releases page.
2.  Download the latest `TransitFinder.zip` file from the "Assets" section.
3.  Extract the `.zip` file to any location on your computer.
4.  Open the newly created `TransitFinder` folder and double-click `TransitFinder.exe` to run the application.

---

## Acknowledgements

*   **AI-Assisted Development**: This project's development was accelerated by leveraging Google's **Gemini 2.0 Flash** and **Gemini 2.5 Pro** models for tasks such as code optimization and documentation generation.
*   **Data Sources & Scientific Models**:
    *   The foundational vector map layers (coastlines, borders, etc.) are sourced from [**Natural Earth**](https://www.naturalearthdata.com/).
    *   The comprehensive database of airports, runways, and navaids is provided by the [**OurAirports**](https://davidmegginson.github.io/ourairports-data/) community project.
    *   Celestial body positions are calculated using the **JPL DE421 ephemeris** provided by NASA.
    *   Geodetic calculations adhere to the **WGS84** Earth ellipsoid model.
*   **ADS-B Decoding**: The software bundles and utilizes **dump1090**, an open-source ADS-B decoder written by Salvatore Sanfilippo (antirez@gmail.com) and distributed under its original **BSD 3-Clause license**.

---

## License

This project is licensed under the [MIT License](LICENSE).