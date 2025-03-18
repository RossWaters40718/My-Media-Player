import tkinter as tk
from tkinter import *
from tkinter.ttk import *
from tkinter import ttk, font, filedialog, messagebox
import re
import os
import cv2
import json
import time
import psutil
import win32con
import win32gui
import win32api
import requests
import subprocess
import win32process
from pathlib import Path
from numpy import round, sin, cos, radians, random
from pynput import keyboard
from pynput.keyboard import Key, Controller
from threading import Timer
from time import perf_counter_ns
from pyaudio import PyAudio # Only Used To Retrieve Default Audio Output Device
from pygame import mixer, _sdl2 # Pygame Only Used To Retrieve All Audio Output Devices
from ctypes import cast, POINTER
from comtypes import CLSCTX_ALL
from pycaw.pycaw import AudioUtilities, IAudioEndpointVolume
import pywinctl as window
from win32api import GetMonitorInfo, MonitorFromPoint
from send2trash import send2trash# Recycle Bin
from collections import Counter
from moviepy.video.io.ffmpeg_tools import ffmpeg_merge_video_audio
from pytubefix import YouTube
from pytubefix import Stream
CANCEL_PREFIX = "Cancel"

class FFPLAY():
    def __init__(self,parent):
        self.parent=parent
        self.ffplay_window=None# ffplay Window
        self.handle=None
        self.process_ffplay=None# ffmplay Process
        self.ffplay_running=False# ffplay Process Status
        self.cv2_running=False# CV2 Image Status
        self.click_next=False# Media File Finished, Simulate Next Button Click
        self.next_ready=True
        self.timer=None# Timer Thread For Slider Clock
        self.timer_running=False# Timer Thread Status
        self.listener=None# Keyboard Listener
        self.Media_Dict={}# Shuffled Or UnShuffled Song,Video,Image Dictionary
        self.Original_Dict={}# Original Sorted Unshuffled
        self.active_database=""
        self.active_media=""
        self.active_file=""
        self.initial_sound_device=""
        self.key_now=None# Active Media File Key
        self.last_key=None
        self.repeat=False
        self.shuffled=False
        self.seeking=False
        self._duration=0
        self._start_time=0.0
        self._interval=0.1
        self._time_now=0.0
        self._elapsed_time=0.0
        self._paused_time=0.0
        self._factor=1.0
        self._ns_time=0
        self.trough=False
        self.muted=False
        self.paused=False
        self.show_modes=["video","waves","rdft"]
        self.showmode=self.show_modes[0]
        self.showmode_change=True
        self.slider_clicked=False
        devices=AudioUtilities.GetSpeakers()# Initialize Master Volumn Slider
        self.interface=devices.Activate(IAudioEndpointVolume._iid_, CLSCTX_ALL, None)
        # Initialize Scroll Window
        self.scroll_window=tk.Frame(parent)
        self.scroll_window.config(bg="#bcbcbc",relief="raised",borderwidth=6)
        self.scroll_window.pack(side=LEFT, anchor=NW, fill=BOTH, expand=TRUE, padx=(6,0), pady=(0,6))
        self.vbar=ttk.Scrollbar(self.scroll_window,orient='vertical')
        self.vbar.pack(side=RIGHT,fill=Y,expand=TRUE,padx=(0,0),pady=(0,0))                                        
        self.ybar=ttk.Scrollbar(self.scroll_window,orient='horizontal')
        self.ybar.pack(side=BOTTOM,fill=Y,expand=FALSE,padx=(0,0),pady=(0,0))                                        
        self.media_list=Listbox(self.scroll_window,foreground="#ffffff",background="#000000",selectbackground="#4cffff",
                                selectforeground="#000000",width=45,font=media_font,yscrollcommand=self.vbar.set )  
        self.media_list.pack(side=TOP,anchor=NW,fill=BOTH,expand=True,padx=(0,0),pady=(0,0))                     
        pgm_path=Path(__file__).parent.absolute()
        self.music_path=os.path.join(pgm_path,"Music.json")
        self.music_favorite_path=os.path.join(pgm_path,"Music_Favorite.json")
        self.video_path=os.path.join(pgm_path,"Videos.json")
        self.video_family_path=os.path.join(pgm_path,"Videos_Family.json")
        self.video_favorite_path=os.path.join(pgm_path,"Videos_Favorite.json")
        self.video_music_path=os.path.join(pgm_path,"Videos_Music.json")
        self.video_karaoke_path=os.path.join(pgm_path,"Videos_Karaoke.json")
        self.picture_path=os.path.join(pgm_path,"Pictures.json")
        self.picture_family_path=os.path.join(pgm_path,"Pictures_family.json")
        self.picture_favorite_path=os.path.join(pgm_path,"Pictures_favorite.json")
        self.setup_path=os.path.join(pgm_path,"Setup.json")
        self.download_path=os.path.join(os.path.expanduser("~"),"youtube_downloads.json")
        self.readme_path=os.path.join(pgm_path,"Bound Keys.txt")
        # Create json Database Files If Not Exist
        db_paths=[self.music_path,self.music_favorite_path,self.video_path,self.video_family_path,self.video_favorite_path,self.video_music_path,
                self.video_karaoke_path,self.picture_path,self.picture_family_path,self.picture_favorite_path,self.setup_path]
        for k in range(len(db_paths)):# Create Media Databases 
            if not os.path.exists(db_paths[k]):
                temp_dict={}
                with open(db_paths[k], "w") as json_file:
                    json.dump(temp_dict, json_file)
                json_file.close()
        # Create All Media Folders
        self.music_folder=os.path.join(Path.home(),"Music")
        self.music_favorite_folder=os.path.join(Path.home(),"Music Favorite")
        self.picture_folder=os.path.join(Path.home(),"Pictures")
        self.picture_family_folder=os.path.join(Path.home(),"Pictures_Family")
        self.picture_favorite_folder=os.path.join(Path.home(),"Pictures_Favorite")
        self.video_folder=os.path.join(Path.home(),"Videos")
        self.video_family_folder=os.path.join(Path.home(),"Videos_Family")
        self.video_music_folder=os.path.join(Path.home(),"Videos_Music")
        self.video_favorite_folder=os.path.join(Path.home(),"Videos_Favorite")
        self.video_karaoke_folder=os.path.join(Path.home(),"Videos_Karaoke")
        # Create Media Folders If Not Exist
        folder_paths=[self.music_folder,self.music_favorite_folder,self.video_folder,self.video_family_folder,self.video_favorite_folder,
                self.video_music_folder,self.video_karaoke_folder,self.picture_folder,self.picture_family_folder,self.picture_favorite_folder]
        for k in range(len(folder_paths)):# Create Media Databases 
            if not os.path.exists(folder_paths[k]):
                os.makedirs(folder_paths[k])
      # Define All File Extensions
        self.ffmpeg_audio_exts=['mp3','wma','wav','mp2','ac3','aac','eac3','m4a','wmav1','wmav2','opus','ogg','aiff','alac','ape','flac']
        self.ffmpeg_video_exts=['mp4','avi','mov','mkv','mpg','mpeg','wmv','webm','flv','mj2','3gp','3g2']
        self.ffmpeg_image_exts=['bmp','jpg','jpeg','gif','png','ppm','dib']
    def get_music_metadata(self,file,data):# Can Return title, artist, album, genre, track or bitrate
        try:
            if data=="bitrate":
                proc=subprocess.Popen(["ffprobe","-v","0","-select_streams","a:0","-show_entries","stream=bit_rate","-of","compact=p=0:nk=1", file],
                                    stdout=subprocess.PIPE,creationflags=subprocess.CREATE_NO_WINDOW)
            else:    
                data=f"format_tags={data}"
                proc=subprocess.Popen(["ffprobe","-v","error","-of","csv=s=x:p=0","-show_entries",data,file],
                                    stdout=subprocess.PIPE,creationflags=subprocess.CREATE_NO_WINDOW)
            stdout,_=proc.communicate()
            proc.terminate()
            output=stdout.strip()# Capture the standard output as a string
            return_data=output.decode()
            return return_data
        except Exception as e:
            title='<FFPROBE Get Album, Artist Or Title>'
            msg1='Retrieving Album, Artist Or Title Failed!\n'
            msg2=f"Error: '{e}'"
            messagebox.showerror(title, msg1+msg2)
            self._stop()                
            return None
    def get_duration(self,file):# minutes = "-sexagesimal", seconds = Blank
        try:
            proc=subprocess.Popen(["ffprobe","-i",file,"-show_entries","format=duration","-v","quiet","-of","csv=p=0"], 
                                stdout=subprocess.PIPE,stderr=subprocess.PIPE,creationflags=subprocess.CREATE_NO_WINDOW)
            stdout,stderr=proc.communicate()
            proc.terminate()
            output=stdout.strip()# Capture the standard output as a string
            video_length=output.decode()[:-1]
            err=(stderr.decode()[:-1])
            if err!='' or video_length=='' or proc.returncode!=0:# Try Different Approach
                proc=subprocess.Popen(["ffprobe","-v","error","-select_streams","v:0","-show_entries","stream=duration","-of","default=noprint_wrappers=1:nokey=1",file], 
                                        stdout=subprocess.PIPE,stderr=subprocess.PIPE,creationflags=subprocess.CREATE_NO_WINDOW)
                stdout,stderr=proc.communicate()
                proc.terminate()
                output=stdout.strip()# Capture the standard output as a string
                video_length=output.decode()[:-1]
                err=(stderr.decode()[:-1])
                if err!='' or video_length=='' or proc.returncode!=0:raise Exception("ffprobe Get Stream Duration")# Try Different Approach
            video_length=round(float(video_length),3)
            return video_length,err
        except Exception as e:
            return None,err
    def begin_seeking(self,event):
        clicked=time_scale.identify(event.x, event.y)
        if clicked=="":
            self.slider_clicked=True
            return
        if self.ffplay_running:
            if clicked=="trough1":
                self.trough=True
                self.send_keyboard_key("left")
                if self._time_now-10<0.0:self._time_now=0.0
                else:self._time_now-=10
            elif clicked=="trough2":
                self.trough=True
                self.send_keyboard_key("right")
                if self._time_now+10>self._duration:self._time_now=self._duration
                else: self._time_now+=10
            elif clicked=="slider": 
                self.pause(self)
                self.seeking=True
        elif self.cv2_running:
            if int(Slide_Show_Delay.get())<=10:
                if clicked=="slider": 
                    self.pause(self)
                    self.seeking=True
            elif int(Slide_Show_Delay.get())>10 and clicked=="trough2":
                if int(Slide_Show_Delay.get())-self._time_now>10:
                    self._time_now+=10
            elif int(Slide_Show_Delay.get())>10 and clicked=="trough1":
                if self._time_now>10:
                    self._time_now-=10
    def end_seeking(self,event):
        unclicked=time_scale.identify(event.x, event.y)
        if self.trough==True or self.slider_clicked:
            self.trough=False
            self.slider_clicked=False
            return
        if self.ffplay_running:
            if unclicked=="slider" or unclicked=="": 
                basename=os.path.basename(self.active_file)
                ext=str(os.path.splitext(basename)[1].replace(".",""))
                if ext.lower() in self.ffmpeg_image_exts:
                    time_scale.set(0.0)
                    self._start_time=time_scale.get()
                    return# Image File
                self._start_time=time_scale.get()
                self._time_now=float(self._start_time)
                self.pause(self)
                self._stop(True)
                self.seeking=False
                if self.shuffled:
                    shuffle_btn.configure(background="#00ffff",foreground="#4cffff")# Active)
                    play_btn.configure(background="#bcbcbc",foreground="#ffffff")# Disabled)
                    stop_btn.configure(background="#bcbcbc",foreground="#ffffff")# Disabled
                else:
                    play_btn.configure(background="#00ffff",foreground="#4cffff")# Active)
                    stop_btn.configure(background="#bcbcbc",foreground="#ffffff")# Disabled
                    shuffle_btn.configure(background="#bcbcbc",foreground="#ffffff")# Disabled)
                root.update()
                self.next_ready=True
                if self.active_media=="music" or self.active_media=="video":self.play_av(self.active_file,self.key_now)
                elif self.active_media=="picture":self.play_images(self.active_file,self.key_now)
        elif self.cv2_running and int(Slide_Show_Delay.get())<=10:
            if unclicked=="slider" or unclicked=="": 
                pos=time_scale.get()
                self._start_time=pos
                self._time_now=float(pos)
                self.pause(self)
                self.seeking=False
        elif self.cv2_running and int(Slide_Show_Delay.get())==0:
            time_scale.set(0.0)
            time_scale.update()
    def bound_keys(self,key):
        if key.keysym=="XF86AudioPlay":self.ctrl_btn_clicked(self,"btn play")
        elif key.keysym=="XF86AudioPrev":self.ctrl_btn_clicked(self,"previous")
        elif key.keysym=="XF86AudioNext":self.ctrl_btn_clicked(self,"next")
        elif key.keysym=="p" or key.keysym=="P" or key.keysym=="XF86AudioPause":self.pause(self)
        elif key.keysym=="r" or key.keysym=="R":self.ctrl_btn_clicked(self,"repeat")
        elif key.keysym=="m" or key.keysym=="M" or key.keysym=="XF86AudioMute":self.ctrl_btn_clicked(self,"mute")
        elif key.keysym=="q" or key.keysym=="Q" or key.keysym=="Escape":self.ctrl_btn_clicked(self,"stop")
        elif key.keysym=="e" or key.keysym=="E":self.destroy()
        elif key.keysym=="XF86AudioLowerVolume":
            level=self.Master_Volume.GetMasterVolumeLevelScalar()# Volume Slider Level / 100
            Level.set(level*100)# Track Volume From Other Sliders (Windows, Sound Card)
        elif key.keysym=="XF86AudioRaiseVolume":
            level=self.Master_Volume.GetMasterVolumeLevelScalar()# Volume Slider Level / 100
            Level.set(level*100)# Track Volume From Other Sliders (Windows, Sound Card)
        elif key.keysym=="Right":
            self.send_keyboard_key("right")
            if self._time_now+10>self._duration:self._time_now=self._duration
            else: self._time_now+=10
        elif key.keysym=="Left":     
            self.send_keyboard_key("left")
            if self._time_now-10<0.0:self._time_now=0.0
            else:self._time_now-=10
        elif key.keysym=="Up":     
            self.send_keyboard_key("up")
            if self._time_now+60>self._duration:self._time_now=self._duration
            else: self._time_now+=60
        elif key.keysym=="Down":     
            self.send_keyboard_key("down")
            if self._time_now-60<0.0:self._time_now=0.0
            else:self._time_now-=60
        elif key.keysym=="f" or key.keysym=="F":self.send_keyboard_key("full screen")     
        elif key.keysym=="w" or key.keysym=="W":self.send_keyboard_key("showmode")
    def on_release(self,key):
        if self.active_media!="picture" and Slide_Show_Delay.get()=="0":return
        try:
            if key.name=="esc":#Stop Slide Show
                self.listener.stop()
                root.update()
                self._stop()
                return False
        except Exception:
            pass
        try:
            if key.name=="media_play_pause":
                self.pause(self)
                return
        except Exception:
            pass
        try:
            if key.char=="p":
                self.pause(self)
                return
        except Exception:
            pass
        try:
            if key.name=="media_previous":
                self.cv2_running==False
                self.ctrl_btn_clicked(self,"previous")
                return
        except Exception:
            pass
        try:
            if key.name=="media_next":
                self.cv2_running==False
                self.ctrl_btn_clicked(self,"next")
                return
        except Exception:
            pass
        try:
            if key.name=="media_volume_up":
                level=self.Master_Volume.GetMasterVolumeLevelScalar()# Volume Slider Level / 100
                Level.set(level*100)# Track Volume From Other Sliders (Windows, Sound Card)
                return
        except Exception:
            pass
        try:
            if key.name=="media_volume_down":
                level=self.Master_Volume.GetMasterVolumeLevelScalar()# Volume Slider Level / 100
                Level.set(level*100)# Track Volume From Other Sliders (Windows, Sound Card)
                return
        except Exception:
            pass
        try:
            if key.name=="media_volume_mute":
                self.ctrl_btn_clicked(self,"mute")
                return
        except Exception:
            pass
        try:
            if key.name=="right":
                if self._time_now+10>float(Slide_Show_Delay.get()):self._time_now=float(Slide_Show_Delay.get())
                else: self._time_now+=10
                return
        except Exception:
            pass
        try:
            if key.name=="left":
                if self._time_now-10<0.0:self._time_now=0.0
                else:self._time_now-=10
                return
        except Exception:
            pass
        try:
            if key.char=="r":
                self.ctrl_btn_clicked(self,"repeat")
                return
        except Exception:
            pass
        try:
            if key.char=="f":
                return
        except Exception:
            pass
        try:
            if key.char=="q":
                self.listener.stop()
                root.update()
                self._stop()
                return False
        except Exception:
            pass
    def set_window_coord(self,wid,hgt):
        if Screen_Position.get()=="Top Left":_x,_y=0,0
        elif Screen_Position.get()=="Top Center":_x,_y=int((work_area[2]/2)-(int(wid)/2)),0
        elif Screen_Position.get()=="Top Right":_x,_y=work_area[2]-int(wid),0
        elif Screen_Position.get()=="Center Left":_x,_y=0,int((work_area[3]/2)-(int(hgt)/2))
        elif Screen_Position.get()=="Center":_x,_y=int((work_area[2]/2)-(int(wid)/2)),int((work_area[3]/2)-(int(hgt)/2))
        elif Screen_Position.get()=="Center Right":_x,_y=int((work_area[2])-(int(wid))),int((work_area[3]/2)-(int(hgt)/2))
        elif Screen_Position.get()=="Bottom Left": _x,_y=0,work_area[3]-(int(hgt))
        elif Screen_Position.get()=="Bottom Center": _x,_y=int((work_area[2]/2)-(int(wid)/2)),work_area[3]-(int(hgt))
        elif Screen_Position.get()=="Bottom Right": _x,_y=int((work_area[2])-(int(wid))),work_area[3]-(int(hgt))
        return _x,_y    
    def play_images(self,file,key):# Images/Photos etc...
        if self.next_ready:
            self.key_now=key
            self.next_ready=False
            self.active_file=file
            if not self.cv2_running:# Not Running
                self.click_next=False
                stop_btn.configure(background="#bcbcbc",foreground="#ffffff")# Disabled))
                self.media_list.select_set(key)
                self.media_list.update()
                self._reset_timer()
            self.listener=keyboard.Listener(on_release=self.on_release)
            self.listener.start()
            time.sleep(0.1)
            if int(Slide_Show_Delay.get())==0:self.load_image_menu()
            elif int(Slide_Show_Delay.get())>0:self.update_time_scale(float(Slide_Show_Delay.get()))
            try: 
                cv2.destroyAllWindows()
            except Exception:
                pass
            while self.listener.running and self.key_now!=None :
                try:
                    stop_btn.configure(background="#bcbcbc",foreground="#ffffff")# Disabled
                    title_lbl.configure(text=f"Now Showing: {os.path.basename(self.Media_Dict[str(self.key_now)])}")
                    self.media_list.select_set(self.key_now)
                    self.media_list.update()
                    img=cv2.imread(file,cv2.IMREAD_UNCHANGED)
                    self.active_file=file
                    window_hgt=Screen_Height.get()
                    hgt, wid=img.shape[:2]
                    img_aspect_ratio=wid/hgt
                    if hgt>window_hgt:hgt=window_hgt
                    scale_factor=int(window_hgt)/hgt  # Percent of original size
                    window_hgt=int(hgt * scale_factor)
                    if window_hgt<hgt:window_hgt=hgt
                    window_wid=int(window_hgt * img_aspect_ratio)
                except Exception:
                    self.remove_media_file(key,False)# Remove corrupted Image File From Library
                    continue
                if window_wid>work_area[2]:window_wid=work_area[2]
                if window_hgt>work_area[3]:window_hgt=work_area[3]
                window_x,window_y=self.set_window_coord(window_wid,window_hgt)
                try:
                    window_title=f"My Media Player: Playing {file}"
                    if self.key_now==0:self.media_list.yview_moveto((1/len(self.Media_Dict))*self.key_now)
                    else:self.media_list.yview_moveto((1/len(self.Media_Dict))*(self.key_now-1))# @ 2 down to show previous song
                    self.media_list.update()
                    if self.active_media=="picture":
                        try:
                            dim=(window_wid, window_hgt)
                            resized_img=cv2.resize(img,dim,interpolation=cv2.INTER_AREA)
                            cv2.setWindowTitle("My Media Player", window_title)
                            cv2.imshow("My Media Player", resized_img)
                            self.ffplay_window=window.getWindowsWithTitle(window_title)[0]# Window
                            self.handle=win32gui.FindWindow(None, window_title)# Window Handle
                            win32gui.MoveWindow(self.handle, window_x, window_y, window_wid, window_hgt, 1)
                            cv2.waitKey(1)
                            self.cv2_running=True
                            self.next_ready=True
                            self.ffplay_running=False
                            Start_Time.set(perf_counter_ns())
                            self._time_now=0.0
                            self._factor=1
                            self.last_key=self.key_now
                            self.ffplay_window.activate()
                            if int(Slide_Show_Delay.get())==0:time_delay=300# 5 Minutes If Slide_Show_Delay=0
                            elif int(Slide_Show_Delay.get())>0:time_delay=int(Slide_Show_Delay.get()) 
                            if time_delay>0:# Time Loop For Catching Button Press's Stop Or Quit 
                                while self._time_now<time_delay and self.listener.running:
                                    time.sleep(0.1)
                                    if self.paused:# self._factor Is Correction For Paused Time For Slider
                                        self._paused_time=perf_counter_ns()
                                        self._factor=self._ns_time/self._paused_time
                                        root.update()
                                    else:
                                        self._ns_time=perf_counter_ns()*self._factor
                                        self._elapsed_time=(self._ns_time-Start_Time.get())/1000000000
                                        self._time_now+=self._elapsed_time
                                        if time_delay<=120:time_scale.set(float(self._time_now))
                                        Start_Time.set(Start_Time.get()+(self._elapsed_time*1000000000))
                                        root.update()
                                        if self.key_now!=self.last_key:break
                                cv2.destroyAllWindows()        
                                if self.key_now!=self.last_key and self.key_now!=None:
                                    self.media_list.selection_clear(0, END)
                                    if not self.repeat:
                                        file=self.Media_Dict[str(self.key_now)]
                                    else:
                                        self.key_now=self.last_key
                                        file=self.Media_Dict[str(self.last_key)]        
                                elif self.key_now!=None:
                                    self.media_list.selection_clear(0, END)
                                    if not self.repeat:
                                        if self.key_now==len(self.Media_Dict)-1:
                                            file=self.Media_Dict["0"]
                                            self.key_now=0
                                        else:    
                                            self.key_now+=1
                                            file=self.Media_Dict[str(self.key_now)]
                                    else:file=self.Media_Dict[str(self.key_now)]
                                root.update()        
                            else:self.listener.stop()
                        except Exception:
                            cv2.destroyAllWindows()
                            self.remove_media_file(key,False)# Remove corrupted Image File From Library
                            continue
                except Exception:
                    self.listener.stop()
                    cv2.destroyAllWindows()
                    self._stop()
            self.listener.stop()        
            cv2.destroyAllWindows()
    def play_av(self,file,key):# Audio/Video Files
        if self.next_ready:
            self.key_now=key
            self.next_ready=False
            self.active_file=file
            if not self.ffplay_running:# Not Running
                self.click_next=False
                stop_btn.configure(background="#bcbcbc",foreground="#ffffff")# Disabled
                self._reset_timer()
                title_lbl.configure(text=f"Now Playing: {os.path.basename(self.Media_Dict[str(self.key_now)])}")
                try:
                    self._duration,error=self.get_duration(file)# Duration In Seconds
                    if self._duration==None:raise Exception(error)
                    self.update_time_scale(self._duration)
                    window_hgt=str(Screen_Height.get())
                    window_wid=str(int(Screen_Height.get()*aspect_ratio))   
                    if int(window_wid)>work_area[2]:window_wid=str(work_area[2])
                    if int(window_hgt)>work_area[3]:window_hgt=str(work_area[3])
                    window_x,window_y=self.set_window_coord(window_wid,window_hgt)
                    window_title=f"My Media Player: Playing {file}"
                    if key==0:self.media_list.yview_moveto((1/len(self.Media_Dict))*key)
                    else:self.media_list.yview_moveto((1/len(self.Media_Dict))*(key-1))# @ 2 down to show previous song
                    self.media_list.selection_clear(0, END)
                    self.media_list.select_set(key)
                    self.media_list.update()
                    if self.active_media=="video":
                        self.showmode_change=True
                        self.process_ffplay=subprocess.Popen(["ffplay","-ss",str(self._start_time),"-t",str(self._duration),"-x",window_wid,"-y",
                                                            window_hgt,"-autoexit",file,"-window_title", window_title],
                                                            stdin=subprocess.PIPE,stdout=subprocess.PIPE,creationflags=subprocess.CREATE_NO_WINDOW)
                    elif self.active_media=="music":
                        title=self.get_music_metadata(file,"title")# Get Song title. If Missing title, Do Not Use -showmode Because Error Generated At GetWindowTitle
                        if title=="":# No title
                            self.showmode_change=False
                            self.process_ffplay=subprocess.Popen(["ffplay","-ss",str(self._start_time),"-t",str(self._duration),"-x",
                                                                window_wid,"-y",window_hgt,"-autoexit",file,"-window_title",window_title],
                                                                stdin=subprocess.PIPE,stdout=subprocess.PIPE,creationflags=subprocess.CREATE_NO_WINDOW)
                        else:# title exist
                            self.showmode_change=True
                            self.process_ffplay=subprocess.Popen(["ffplay","-i","-ss",str(self._start_time),"-t",str(self._duration),"-x",window_wid,"-y",
                                                                window_hgt,"-showmode",self.showmode,file,"-autoexit","-window_title",window_title],
                                                                stdin=subprocess.PIPE,stdout=subprocess.PIPE,creationflags=subprocess.CREATE_NO_WINDOW)
                    if self.showmode_change:
                        self.load_music_menu()
                    else:root.config(menu="")    
                    poll=""
                    count=0# Exit Backup
                    while poll!=None and count<=40:# 40 = 4 Seconds Max Time For Loop
                        count+=1
                        try:
                            time.sleep(0.1)
                            poll=self.process_ffplay.poll()
                        except Exception as e:
                            pass
                    if count>=40:raise Exception(e)
                    if poll==None:# None = ffplay Running
                        Start_Time.set(perf_counter_ns())
                        self.ffplay_running=True
                        self.cv2_running=False
                        ready=False
                        count=0# Exit Backup
                        while ready==False and count<=40:# 40 = 4 Seconds Max Time For Loop
                            count+=1
                            try:
                                time.sleep(0.1)
                                self.ffplay_window=window.getWindowsWithTitle(window_title)[0]# Window
                                if self.ffplay_window is not None:ready=True
                            except Exception as e:
                                pass
                        if count>=40:raise Exception("getWindowsWithTitle()")# Allow 4 Seconds        
                        self.handle=win32gui.FindWindow(None, window_title)# Window Handle
                        win32gui.MoveWindow(self.handle, window_x, window_y, int(window_wid), int(window_hgt), 1)
                        self.ffplay_window.activate()
                        if not self.timer_running:
                            self._start_timer_thread()
                    else:raise Exception("ffplay Not Running")
                except Exception as e:
                    if self.ffplay_running:
                        self.process_ffplay.terminate()
                        self.process_ffplay.kill()
                        self.ffplay_running=False
                    self.next_ready=True
                    self.remove_media_file(self.key_now)# Remove File And Go To Next File
    def _start_timer_thread(self):
        self.next_ready=True
        if self.click_next==True:
            self.ctrl_btn_clicked(self,"next")
        else:
            self.timer=Timer(self._interval, self._update_timer)
            self.timer_running=True
            self.timer.start()
    def _update_timer(self):
        root.focus_force()
        if self.timer_running==False or self.ffplay_running==False and self.cv2_running==False:return 
        if self.paused:# self._factor Is Correction For Paused Time For Slider
            self._paused_time=perf_counter_ns()
            self._factor=self._ns_time/self._paused_time
        else:
            self._ns_time=perf_counter_ns()*self._factor
            self._elapsed_time=(self._ns_time-Start_Time.get())/1000000000
            self._time_now+=self._elapsed_time
            time_scale.set(float(self._time_now))
            Start_Time.set(Start_Time.get()+(self._elapsed_time*1000000000))
            if self.ffplay_running:
                poll=self.process_ffplay.poll()
                if poll!=None:self.click_next=True# ffplay not running, Terminated By -autoexit, Ready Next File
        level=self.Master_Volume.GetMasterVolumeLevelScalar()# Volume Slider Level / 100
        Level.set(level*100)# Track Volume From Other Sliders (Windows, Sound Card)
        is_muted=self.Master_Volume.GetMute()
        if is_muted and self.muted==False:self.ctrl_btn_clicked(self,"mute")
        elif not is_muted and self.muted==True:self.ctrl_btn_clicked(self,"mute") 
        self._start_timer_thread()
    def _reset_timer(self):        
        Start_Time.set(0.0)
        time_scale.set(float(self._start_time))
        time_scale.update()
        self._interval=0.1
        self.timer_running=False
        self._time_now=self._start_time
        self._elapsed_time=0.0
        self._paused_time=0.0
        self._factor=1.0
        self._ns_time=0
    def stop_process(self):# Used For Advancing Media Files
            if self.timer_running:
                self.timer.cancel()
                self.timer_running=False
            try:    
                if self.ffplay_running:
                    poll=self.process_ffplay.poll()
                    while poll==None:
                        self.send_keyboard_key("quit")
                        poll=self.process_ffplay.poll()
                    self.process_ffplay.terminate()
                    self.process_ffplay.kill()
                    self.ffplay_running=False
                if self.key_now!=None:
                    self.last_key=self.key_now
            except Exception:pass
            root.focus_force()
    def _stop(self,skip_menu=None):# Used For Stopping Media File
        if self.cv2_running:
            self.remove_menubar()
            root.update()
            self.cv2_running=False    
        elif self.ffplay_running:
            if self.active_media=="music":self.remove_menubar()
            self.stop_process()
        if not self.seeking:
            title_lbl.configure(text="")
            time_scale.set(0.0)
            self.update_time_scale(0.0)    
            self.last_key=self.key_now
            play_btn.configure(background="#bcbcbc",foreground="#ffffff")# Disabled
            shuffle_btn.configure(background="#bcbcbc",foreground="#ffffff")# Disabled
            stop_btn.configure(background="#00ffff",foreground="#ff0000")# Active
            pause_btn.configure(background="#bcbcbc",foreground="#ffffff")# Disabled
            self.paused=False
            self.Master_Volume.SetMute(False, None)
            mute_btn.config(text="\U0001F50A",background="#bcbcbc",foreground="#ffffff")# Disabled
            self.muted=False
            if skip_menu==None :self.load_menubar()
            if self.key_now==None:return
            self.media_list.selection_clear(0, END)
            self.key_now=None
            self.last_key=None
            self.media_list.yview_moveto(0)
            root.update()
    def update_time_scale(self,sec):
        sec=round(sec) 
        interval=sec/10
        time_scale.config(from_=0.0,to=sec)
        time_scale.config(tickinterval=(interval))
        time_scale.config(resolution=0.01)
    def remove_menubar(self):
        try:
            self.menubar.delete(0, END)
            empty_menu=Menu(root)
            root.config(menu=empty_menu)
            root.update()
        except Exception:pass
    def send_keyboard_key(self,key):
        keyboard=Controller()
        mykeys=[Key.left,Key.right,Key.up,Key.down,"p","q","w","s","f"]
        if self.ffplay_running:self.ffplay_window.activate()
        if key=="left":key_now=mykeys[0]
        elif key=="right":key_now=mykeys[1]
        elif key=="up":key_now=mykeys[2]
        elif key=="down":key_now=mykeys[3]
        elif key=="pause":key_now=mykeys[4]
        elif key=="quit":key_now=mykeys[5]
        elif key=="showmode":key_now=mykeys[6]
        elif key=="stop":key_now=mykeys[7]
        elif key=="full screen":key_now=mykeys[8]
        keyboard.press(key_now)
        time.sleep(0.1)
        keyboard.release(key_now)
    def slider_released(self):
        try:
            if self.ffplay_running:self.ffplay_window.activate()
        except Exception:pass
    def set_master_volume(self):
        self.Master_Volume.SetMasterVolumeLevelScalar(Level.get()/100, None)
        level=self.Master_Volume.GetMasterVolumeLevelScalar()# Volume Slider Level / 100
        if level==0:self.Master_Volume.SetMute(True, None)
        else:self.Master_Volume.SetMute(False, None)
    def ctrl_btn_clicked(self,event,btn):
        if self.Media_Dict:
            if btn=="btn play":
                if self.shuffled:
                    if self.paused:self.pause(self)
                    if self.ffplay_running:self.stop_process()
                    if self.cv2_running:self.listener.stop()
                    self.shuffled=False
                    self.load_library(self.active_database)
                else:
                    if self.ffplay_running or self.cv2_running:return# If Playing, Do Nothing
                self._start_time=0.0
                play_btn.configure(background="#00ffff",foreground="#4cffff")# Active
                play_btn.update()
                stop_btn.configure(background="#bcbcbc",foreground="#ffffff")# Disabled
                shuffle_btn.configure(background="#bcbcbc",foreground="#ffffff")# Disabled
                root.update()
                file=self.Media_Dict["0"]
                self.key_now=0
                if self.active_media=="music" or self.active_media=="video":self.play_av(file,self.key_now)
                elif self.active_media=="picture":self.play_images(file,self.key_now)
            elif btn=="media play":# File Clicked In Window
                if self.paused:self.pause(self)
                if self.ffplay_running:self.stop_process()
                if not self.shuffled:
                    play_btn.configure(background="#00ffff",foreground="#4cffff")# Active
                    stop_btn.configure(background="#bcbcbc",foreground="#ffffff")# Disabled
                else:    
                    shuffle_btn.configure(background="#00ffff",foreground="#4cffff")# Active
                    play_btn.configure(background="#bcbcbc",foreground="#ffffff")# Disabled
                root.update()
                self._start_time=0.0
                selection=self.media_list.curselection()
                self.key_now=selection[0]
                file=self.Media_Dict[str(self.key_now)]
                if self.active_media=="music" or self.active_media=="video":self.play_av(file,self.key_now)
                elif self.active_media=="picture":
                    if not self.cv2_running:self.play_images(file,self.key_now)
            elif btn=="shuffled":
                if self.paused:self.pause(self)
                if self.ffplay_running:self.stop_process()
                if self.cv2_running:self.listener.stop()
                self.shuffled=True
                self.load_library(self.active_database)
                self._start_time=0.0
                shuffle_btn.configure(background="#00ffff",foreground="#4cffff")# Active
                play_btn.configure(background="#bcbcbc",foreground="#ffffff")# Disabled
                stop_btn.configure(background="#bcbcbc",foreground="#ffffff")# Disabled
                root.update()
                file=self.Media_Dict["0"]
                self.key_now=0
                if self.active_media=="music" or self.active_media=="video":self.play_av(file,self.key_now)
                elif self.active_media=="picture":self.play_images(file,self.key_now)
            elif btn=="next":
                if self.paused:self.pause(self)
                if self.next_ready:# Prevent Multiple Windows
                    self._start_time=0.0
                    if self.ffplay_running:self.stop_process()
                    if self.last_key!=None:
                        if self.repeat:
                            self.key_now=self.last_key   
                            file=self.Media_Dict[str(self.key_now)]
                        elif self.last_key==len(self.Media_Dict)-1:
                            file=self.Media_Dict["0"]
                            self.key_now=0
                        else:    
                            self.key_now=self.last_key+1    
                            file=self.Media_Dict[str(self.key_now)]
                    else:
                        play_btn.configure(background="#00ffff",foreground="#4cffff")# Active
                        stop_btn.configure(background="#bcbcbc",foreground="#ffffff")# Disabled
                        root.update()
                        file=self.Media_Dict["0"]
                        self.key_now=0
                    if self.active_media=="picture":
                        if not self.cv2_running:self.play_images(file,self.key_now)
                    elif self.active_media=="music" or self.active_media=="video":self.play_av(file,self.key_now)
            elif btn=="previous":
                if self.paused:self.pause(self)
                if self.next_ready:# Prevent Multiple Windows
                    self._start_time=0.0
                    self.click_next=False
                    if self.ffplay_running:self.stop_process()
                    if self.last_key!=None:
                        if self.repeat:
                            self.key_now=self.last_key   
                            file=self.Media_Dict[str(self.key_now)]
                        elif self.last_key!=0:
                            self.key_now=self.last_key-1    
                            file=self.Media_Dict[str(self.key_now)]
                        else:# self.last_key=0
                            self.key_now=len(self.Media_Dict)-1
                            file=self.Media_Dict[str(self.key_now)]
                    else:
                        play_btn.configure(background="#00ffff",foreground="#4cffff")# Active
                        stop_btn.configure(background="#bcbcbc",foreground="#ffffff")# Disabled
                        root.update()
                        file=self.Media_Dict["0"]
                        self.key_now=0
                    if self.active_media=="picture":
                        if not self.cv2_running:self.play_images(file,self.key_now)
                    elif self.active_media=="music" or self.active_media=="video":self.play_av(file,self.key_now)
            elif btn=="repeat":
                if self.cv2_running and int(Slide_Show_Delay.get())==0:return
                self._start_time=0.0
                if self.repeat==False:
                    self.repeat=True
                    repeat_btn.configure(background="#00ffff",foreground="#4cffff")# Active
                    repeat_btn.update()
                else:
                    self.repeat=False   
                    repeat_btn.configure(background="#bcbcbc",foreground="#ffffff")# Disabled
                    repeat_btn.update()
            elif btn=="stop":
                if self.ffplay_running or self.cv2_running:
                    if self.cv2_running:self.listener.stop()
                    root.update()
                    self._stop()
            elif btn=="mute":
                if self.muted==False:
                    self.Master_Volume.SetMute(True, None)
                    mute_btn.config(text="\U0001F507",background="#00ffff",foreground="#ff0000")# Active
                    self.muted=True
                else:# Unmute Clicked
                    self.Master_Volume.SetMute(False, None)
                    mute_btn.config(text="\U0001F50A",background="#bcbcbc",foreground="#ffffff")# Disabled
                    self.muted=False
                root.update()    
    def pause(self,event):
        if self.ffplay_running:
            self.ffplay_window.activate()
            self.send_keyboard_key("pause")
            if self.paused==False:
                self.paused=True
                pause_btn.configure(background="#00ffff",foreground="#4cffff")# Active
            else:
                self.paused=False
                pause_btn.configure(background="#bcbcbc",foreground="#ffffff")# Disabled
        elif self.cv2_running and int(Slide_Show_Delay.get())>0:
            if self.paused==False:
                self.paused=True
                pause_btn.configure(background="#00ffff",foreground="#4cffff")# Active
            else:# Resume Clicked
                self.paused=False
                pause_btn.configure(background="#bcbcbc",foreground="#ffffff")# Disabled
    def destroy(self):
        try:
            self.stop_process()
            if os.path.isfile(soundview_path):# Set Default Audio Output To Original Device    
                cmd=[soundview_path, "/SetDefault", self.initial_sound_device, "1", "/Unmute", self.initial_sound_device, "/SetVolume", self.initial_sound_device, str(Level.get())]
                subprocess.run(cmd, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            self.write_setup()
            self.clear_all()
            for widget in root.winfo_children():# Destroys Menu Bars, Frame, Scroll Bars etc...
                if isinstance(widget, tk.Canvas):widget.destroy()
                else:widget.destroy()
            self.process_ffplay.kill()
            os._exit(0)
        except Exception:
            pass
        os._exit(0)
    def rotate_image(self):
        title="<Image Rotation>"
        msg1="Enter Image Rotation In Degrees.\n"
        msg2="Range Is From -360 To 360 Degrees!\n"
        msg3="A Negative Number Rotates The Image Clock-Wise.\n"
        msg4="A Positive Number Rotates The Image Counter Clock-Wise."
        msg=msg1+msg2+msg3+msg4
        angle=my_askinteger(title,msg,180,-360,360)
        if angle!=None:
            try:
                img=cv2.imread(self.active_file,cv2.IMREAD_UNCHANGED)
                h, w = img.shape[:2]
                center = (w // 2, h // 2)
                abs_cos, abs_sin = abs(cos(radians(angle))), abs(sin(radians(angle)))
                bound_w = int(h * abs_sin + w * abs_cos)
                bound_h = int(h * abs_cos + w * abs_sin)
                rotation_matrix = cv2.getRotationMatrix2D(center, angle, 1.0)
                rotation_matrix[0, 2] += bound_w / 2 - center[0]
                rotation_matrix[1, 2] += bound_h / 2 - center[1]
                rotated_img = cv2.warpAffine(img, rotation_matrix, (bound_w, bound_h))
                cv2.imwrite(self.active_file, rotated_img)
                if self.active_media=="picture":self.play_images(self.active_file,self.key_now)
            except Exception as e:
                title='<Image Rotation>'
                msg1='Rotating Image Failed!\n'
                msg2='This File May Be Corrupted!\n'
                msg3=f"Error: '{e}'"
                msg=msg1+msg2+msg3
                messagebox.showerror(title, msg1+msg2)
    def delete_image_file(self):
        try:
            if len(self.Media_Dict)>0:
                file_to_delete=self.Media_Dict[str(self.key_now)]
                file_name=os.path.basename(file_to_delete)
                if os.path.exists(file_to_delete):
                    path=Path(file_to_delete)
                    send2trash(path)# Recycle Bin
                    title=f'<Delete File {file_name}>'
                    msg=f'{file_name} Was Deleted Successfully!'
                    messagebox.showinfo(title, msg)
                    self.remove_media_file(self.key_now,False)# Remove From Library
        except Exception as e:
            title=f'<Delete File {file_name}>'
            msg1=f'Deleting {file_name} Failed!\n'
            msg2=f"Error: '{e}'"
            msg=msg1+msg2
            messagebox.showerror(title, msg)
    def remove_media_file(self,key=None,show_msg=None):
        try:
            if len(self.Media_Dict)>0:
                if self.cv2_running:self.listener.stop()
                final_key=False
                end_key=False
                file_to_remove=self.Media_Dict[str(self.key_now)]
                file_name=os.path.basename(file_to_remove)
                if self.active_database=="Pictures":db_path=self.picture_path
                elif self.active_database=="Pictures_Family":db_path=self.picture_family_path
                elif self.active_database=="Pictures_Favorite":db_path=self.picture_favorite_path
                elif self.active_database=="Music":db_path=self.music_path
                elif self.active_database=="Music_Favorite":db_path=self.music_favorite_path
                elif self.active_database=="Videos":db_path=self.video_path
                elif self.active_database=="Videos_Family":db_path=self.video_family_path
                elif self.active_database=="Videos_Favorite":db_path=self.video_favorite_path
                elif self.active_database=="Videos_Karaoke":db_path=self.video_karaoke_path
                elif self.active_database=="Videos_Music":db_path=self.video_music_path
                if key==None:key=self.key_now
                dict_len=len(self.Media_Dict)
                end_key=dict_len-1
                if dict_len==0:return
                elif dict_len==1:
                    if self.key_now==end_key:
                        end_key=True
                        final_key=True
                    else:final_key=False
                elif dict_len>1 and self.key_now==end_key:
                    end_key=True
                    final_key=False    
                else:
                    end_key=False
                    final_key=False        
                del self.Media_Dict[str(key)]
                temp_dict=self.Media_Dict.copy()
                self.Media_Dict.clear()
                count=0
                temp_dict2={}
                for _, value in temp_dict.items():
                    temp_dict2[str(count)]=value
                    count+=1
                self.clear_database(self.active_database,False)
                with open(db_path, "w") as outfile:json.dump(temp_dict2, outfile)
                outfile.close()
                if final_key:
                    self.send_keyboard_key("stop")
                    self.listener.stop()
                    self._stop()
                    return
                self.load_library(self.active_database,True)
                if end_key:self.key_now-=1
                self.active_file=self.Media_Dict.get(str(self.key_now))
                self.next_ready=True
                temp_dict.clear()
                temp_dict2.clear()
                if show_msg:
                    if os.path.exists(file_to_remove):
                        title=f'<Remove File {file_name}>'
                        msg=f'{file_name} Was Removed Successfully!'
                        messagebox.showinfo(title, msg)
                if self.active_media=="music" or self.active_media=="video":self.play_av(self.active_file,self.key_now)
                elif self.active_media=="picture":self.play_images(self.active_file,self.key_now)
        except Exception as e:
            title=f'<Remove File {file_name}>'
            msg1=f'Removing {file_name} Failed!\n'
            msg2=f"Error: '{e}'"
            msg=msg1+msg2
            messagebox.showerror(title, msg)
    def move_image(self,to_db):
        try:
            if len(self.Media_Dict)>0:
                self.listener.stop()
                final_key=False
                end_key=False
                file_to_move=self.Media_Dict[str(self.key_now)]
                file_name=os.path.basename(file_to_move)
                self.add_files_to_db(to_db,file_to_move)
                if self.active_database=="Pictures":db_path=self.picture_path
                elif self.active_database=="Pictures_Family":db_path=self.picture_family_path
                elif self.active_database=="Pictures_Favorite":db_path=self.picture_favorite_path
                dict_len=len(self.Media_Dict)
                end_key=dict_len-1
                if dict_len==0:return
                elif dict_len==1:
                    if self.key_now==end_key:
                        end_key=True
                        final_key=True
                    else:final_key=False
                elif dict_len>1 and self.key_now==end_key:
                    end_key=True
                    final_key=False    
                else:
                    end_key=False
                    final_key=False        
                del self.Media_Dict[str(self.key_now)]
                temp_dict=self.Media_Dict.copy()
                self.Media_Dict.clear()
                count=0
                temp_dict2={}
                for _, value in temp_dict.items():
                    temp_dict2[str(count)]=value
                    count+=1
                self.clear_database(self.active_database,False)
                with open(db_path, "w") as outfile:json.dump(temp_dict2, outfile)
                outfile.close()
                if final_key:
                    self.send_keyboard_key("stop")
                    self.listener.stop()
                    self._stop()
                    return
                self.load_library(self.active_database,True)
                if end_key:self.key_now-=1
                self.active_file=self.Media_Dict.get(str(self.key_now))
                self.next_ready=True
                temp_dict.clear()
                temp_dict2.clear()
                if os.path.exists(file_to_move):
                    title=f'<Move Image File To {to_db} Library>'
                    msg=f'{file_name} Was Moved To {to_db} Library Successfully!'
                    messagebox.showinfo(title, msg)
                if self.active_media=="music" or self.active_media=="video":self.play_av(self.active_file,self.key_now)
                elif self.active_media=="picture":self.play_images(self.active_file,self.key_now)
        except Exception as e:
            title=f'<Move Image File To {to_db} Library>'
            msg1=f'Moving {file_name} To {to_db} Library Failed!\n'
            msg2=f"Error: '{e}'"
            msg=msg1+msg2
            messagebox.showerror(title, msg)# utube_console_Downloader requires Python3.1x Installed 
    def youtube_downloader(self):
        youtube=YouTube_GUI()
        youtube.main()
    def update_databases(self):
        try:
            root.deiconify()
            root.update()
            root.focus_force()
            # Check If Download Folder Path Is In Media Player Paths
            temp_dict=json.load(open(self.download_path, "r+"))
            file_names = [value for key, value in temp_dict.items() if int(key) % 2 != 0]# Odds, Names
            file_paths = [value for key, value in temp_dict.items() if int(key) % 2 == 0]# Evens, Paths
            db_list=["Music","Music_Favorite","Videos","Videos_Music","Videos_Family",
                        "Videos_Favorite","Videos_Karaoke","Pictures","Pictures_Family","Pictures_Favorite"]
            msgs=[]
            msg=""
            for j in range(0,len(file_names)):
                db=Path(file_paths[j]).name
                # Download Folder db_name Is In Media Player Path, Add File To Database    
                if db!="" and file_paths[j]!="" and file_names[j]!="":
                    if db in db_list:
                        msgs.append(f"{file_names[j]} Was Added To {db}\n")
                        msg+=msgs[j]
                        self.clear_database(db)
                        self.upload_from_folder(db,"dont ask")
                        root.update()
            if len(msgs)>0: 
                messagebox.showinfo("< YouTube Downloader > (Media Files Added To Databases)", msg)
        except Exception as e:
            root.focus_force()
            root.deiconify()
            return
    def change_showmode(self):
        if self.showmode_change:
            if self.showmode==self.show_modes[0]:self.showmode=self.show_modes[1]
            elif self.showmode==self.show_modes[1]:self.showmode=self.show_modes[2]
            elif self.showmode==self.show_modes[2]:self.showmode=self.show_modes[0]
            self.send_keyboard_key("showmode")
    def load_music_menu(self):
        self.menubar=Menu(root,fg="#000000")# Create Menubar
        showmode_menu=Menu(self.menubar,background='aqua',foreground='black',tearoff=0)
        self.menubar.add_cascade(label=' Show Mode ',menu=showmode_menu)
        showmode_menu.add_command(label='Change Show Mode',command=lambda:self.change_showmode())
        root.config(menu=self.menubar)
        root.update()
    def load_image_menu(self):
        self.menubar=Menu(root,fg="#000000")# Create Menubar
        images_menu=Menu(self.menubar,background='aqua',foreground='black',tearoff=0)
        self.menubar.add_cascade(label=' Edit Picture ',menu=images_menu)
        images_menu.add_command(label='Rotate Picture And Save',command=lambda:self.rotate_image())
        images_menu.add_separator()
        images_menu.add_command(label='Remove Picture From Library',command=lambda:self.remove_media_file(None,True))
        images_menu.add_separator()
        images_menu.add_command(label='Delete Picture To Recycle Bin',command=lambda:self.delete_image_file())
        images_menu.add_separator()
        move_image=Menu(self.menubar,background='aqua',foreground='black',tearoff=0)
        if self.active_database=="Pictures":
            move_image.add_command(label="Move To Picture Family Image Library",command=lambda:self.move_image("Pictures_Family"))
            move_image.add_separator()
            move_image.add_command(label="Move To Picture Favorite Library",command=lambda:self.move_image("Pictures_Favorite"))
        elif self.active_database=="Pictures_Family":
            move_image.add_command(label="Move To Picture Library",command=lambda:self.move_image("Pictures"))
            move_image.add_separator()
            move_image.add_command(label="Move To Picture Favorite Library",command=lambda:self.move_image("Pictures_Favorite"))
        elif self.active_database=="Pictures_Favorite":
            move_image.add_command(label="Move To Picture Library",command=lambda:self.move_image("Pictures"))
            move_image.add_separator()
            move_image.add_command(label="Move To Picture Family Library",command=lambda:self.move_image("Pictures_Family"))
        images_menu.add_cascade(label='Move Picture',menu=move_image)
        root.config(menu=self.menubar)
        root.update()
    def load_menubar(self):
        self.menubar=Menu(root,fg="#000000")# Create Menubar
        music_menu=Menu(self.menubar,background='aqua',foreground='black',tearoff=0)
        self.menubar.add_cascade(label='     Media Libraries   ',menu=music_menu)
        upload_music=Menu(self.menubar,background='aqua',foreground='black',tearoff=0)
        upload_music.add_command(label="Load Music Library",command=lambda:self.load_library("Music"))
        upload_music.add_separator()
        upload_music.add_command(label="Upload Folder To Music Library",command=lambda:self.upload_from_folder("Music"))
        upload_music.add_separator()
        upload_music.add_command(label="Upload File/s To Music Library",command=lambda:self.add_files_to_db("Music"))
        upload_music.add_separator()
        upload_music.add_command(label="Clear Music Library",command=lambda:self.clear_database("Music"))
        music_menu.add_cascade(label='Music Library',menu=upload_music)
        favorite_music=Menu(self.menubar,background='aqua',foreground='black',tearoff=0)
        favorite_music.add_command(label="Load Music Favorite Library",command=lambda:self.load_library("Music_Favorite"))
        favorite_music.add_separator()
        favorite_music.add_command(label="Upload Folder To Music Favorite Library",command=lambda:self.upload_from_folder("Music_Favorite"))
        favorite_music.add_separator()
        favorite_music.add_command(label="Upload File/s To Music Favorite Library",command=lambda:self.add_files_to_db("Music_Favorite"))
        favorite_music.add_separator()
        favorite_music.add_command(label="Clear Music Favorite Library",command=lambda:self.clear_database("Music_Favorite"))
        music_menu.add_cascade(label="Music Favorite Library",menu=favorite_music)
        music_menu.add_separator()
        upload_videos=Menu(self.menubar,background='aqua',foreground='black',tearoff=0)
        upload_videos.add_command(label="Load Video Library",command=lambda:self.load_library("Videos"))
        upload_videos.add_separator()
        upload_videos.add_command(label="Upload Folder To Video Library",command=lambda:self.upload_from_folder("Videos"))
        upload_videos.add_separator()
        upload_videos.add_command(label="Upload File/s To Video Library",command=lambda:self.add_files_to_db("Videos"))
        upload_videos.add_separator()
        upload_videos.add_command(label="Clear Video Library",command=lambda:self.clear_database("Videos"))
        music_menu.add_cascade(label='Video Library',menu=upload_videos)
        favorite_videos=Menu(self.menubar,background='aqua',foreground='black',tearoff=0)
        favorite_videos.add_command(label="Load Video Favorite Library",command=lambda:self.load_library("Videos_Favorite"))
        favorite_videos.add_separator()
        favorite_videos.add_command(label="Upload Folder To Video Favorite Library",command=lambda:self.upload_from_folder("Videos_Favorite"))
        favorite_videos.add_separator()
        favorite_videos.add_command(label="Upload File/s To Video Favorite Library",command=lambda:self.add_files_to_db("Videos_Favorite"))
        favorite_videos.add_separator()
        favorite_videos.add_command(label="Clear Video Favorite Library",command=lambda:self.clear_database("Videos_Favorite"))
        music_menu.add_cascade(label='Video Favorite Library',menu=favorite_videos)
        music_videos=Menu(self.menubar,background='aqua',foreground='black',tearoff=0)
        music_videos.add_command(label="Load Music Videos Library",command=lambda:self.load_library("Videos_Music"))
        music_videos.add_separator()
        music_videos.add_command(label="Upload Folder To Music Videos Library",command=lambda:self.upload_from_folder("Videos_Music"))
        music_videos.add_separator()
        music_videos.add_command(label="Upload File/s To Music Videos Library",command=lambda:self.add_files_to_db("Videos_Music"))
        music_videos.add_separator()
        music_videos.add_command(label="Clear Music Videos Library",command=lambda:self.clear_database("Videos_Music"))
        music_menu.add_cascade(label='Music Videos Library',menu=music_videos)
        karoake_videos=Menu(self.menubar,background='aqua',foreground='black',tearoff=0)
        karoake_videos.add_command(label="Load Karaoke Videos Library",command=lambda:self.load_library("Videos_Karaoke"))
        karoake_videos.add_separator()
        karoake_videos.add_command(label="Upload Folder To Karaoke Videos Library",command=lambda:self.upload_from_folder("Videos_Karaoke"))
        karoake_videos.add_separator()
        karoake_videos.add_command(label="Upload File/s To Karaoke Videos Library",command=lambda:self.add_files_to_db("Videos_Karaoke"))
        karoake_videos.add_separator()
        karoake_videos.add_command(label="Clear Karaoke Videos Library",command=lambda:self.clear_database("Videos_Karaoke"))
        music_menu.add_cascade(label='Karaoke Videos Library',menu=karoake_videos)
        music_menu.add_separator()
        upload_image=Menu(self.menubar,background='aqua',foreground='black',tearoff=0)
        upload_image.add_command(label="Load Picture Library",command=lambda:self.load_library("Pictures"))
        upload_image.add_separator()
        upload_image.add_command(label="Upload Folder To Picture Library",command=lambda:self.upload_from_folder("Pictures"))
        upload_image.add_separator()
        upload_image.add_command(label="Upload File/s To Picture Library",command=lambda:self.add_files_to_db("Pictures"))
        upload_image.add_separator()
        upload_image.add_command(label="Clear Picture Library",command=lambda:self.clear_database("Pictures"))
        music_menu.add_cascade(label='Picture Library',menu=upload_image)
        family_image=Menu(self.menubar,background='aqua',foreground='black',tearoff=0)
        family_image.add_command(label="Load Picture Family Library",command=lambda:self.load_library("Pictures_Family"))
        family_image.add_separator()
        family_image.add_command(label="Upload Folder To Picture Family Library",command=lambda:self.upload_from_folder("Pictures_Family"))
        family_image.add_separator()
        family_image.add_command(label="Upload File/s To Picture Family Library",command=lambda:self.add_files_to_db("Pictures_Family"))
        family_image.add_separator()
        family_image.add_command(label="Clear Picture Family Library",command=lambda:self.clear_database("Pictures_Family"))
        music_menu.add_cascade(label='Picture Family Library',menu=family_image)
        favorite_image=Menu(self.menubar,background='aqua',foreground='black',tearoff=0)
        favorite_image.add_command(label="Load Picture Favorite Library",command=lambda:self.load_library("Pictures_Favorite"))
        favorite_image.add_separator()
        favorite_image.add_command(label="Upload Folder To Picture Favorite Library",command=lambda:self.upload_from_folder("Pictures_Favorite"))
        favorite_image.add_separator()
        favorite_image.add_command(label="Upload File/s To Picture Favorite Library",command=lambda:self.add_files_to_db("Pictures_Favorite"))
        favorite_image.add_separator()
        favorite_image.add_command(label="Clear Picture Favorite Library",command=lambda:self.clear_database("Pictures_Favorite"))
        music_menu.add_cascade(label='Picture Favorite Library',menu=favorite_image)
        music_menu.add_command(label="Picture Slide Show",command=lambda:set_slide_show())
        download_menu=Menu(self.menubar,background='aqua',foreground='black',tearoff=0)
        self.menubar.add_cascade(label='   YouTube Downloader   ',menu=download_menu)
        download_menu.add_command(label="YouTube GUI Downloader",command=lambda:self.youtube_downloader())
        screen_menu=Menu(self.menubar,background='aqua',foreground='black',tearoff=0)#
        self.menubar.add_cascade(label='   Media Screen   ',menu=screen_menu)
        screen_menu.add_command(label='Screen Size',command=lambda:set_screen_size())
        screen_menu.add_separator()
        screen_menu.add_command(label='Startup Position',command=lambda:set_screen_position())
        if os.path.isfile(soundview_path):
            self.device_menu=Menu(self.menubar,background='aqua',foreground='black',tearoff=0)
            self.menubar.add_cascade(label='   Audio Output Devices   ',menu=self.device_menu)
            self.update_devices()
        bound_menu=Menu(self.menubar,background='aqua',foreground='black',tearoff=0)
        self.menubar.add_cascade(label='   Read Me   ',menu=bound_menu)
        bound_menu.add_command(label="View Bound Keyboard Keys",command=lambda:subprocess.Popen(["notepad.exe", self.readme_path]))
        about_menu=Menu(self.menubar,background='aqua',foreground='black',tearoff=0)
        self.menubar.add_cascade(label='   About   ',menu=about_menu)
        about_menu.add_command(label='About My Media Player',command=lambda:about())
        root.config(menu=self.menubar)
        root.update()
    def init_audio(self):
        try:
            default_device=PyAudio().get_default_output_device_info()["name"]
            devices=self.get_devices()
            PyAudio().terminate()
            result=list(filter(lambda x: default_device in x, devices))
            self.Active_Device=result[0]
            if self.Active_Device=="":
                self.Active_Device="Default"
            if os.path.isfile(soundview_path):    
                self.initial_sound_device=self.Active_Device.split("(", 1)[0].replace(" ","")
                cmd=[soundview_path, "/SetDefault", self.initial_sound_device, "1", "/Unmute", self.initial_sound_device, "/SetVolume", self.initial_sound_device, str(Level.get())]
                subprocess.run(cmd, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            devices=AudioUtilities.GetSpeakers()# Initialize Master Volumn Slider
            self.interface=devices.Activate(IAudioEndpointVolume._iid_, CLSCTX_ALL, None)
            self.Master_Volume=cast(self.interface, POINTER(IAudioEndpointVolume))
            Level.set(5)
            self.Master_Volume.SetMasterVolumeLevelScalar(Level.get()/ 100, None)
            self.muted=False
            self.paused=False
        except Exception as ex:
            title='<Interface Initialization>'
            msg1='Initialization Failed. Ending Program!\n'
            msg2=f"Error: '{ex}'"
            messagebox.showerror(title, msg1+msg2)
            self.destroy()
    def clear_database(self,db,change=True):
        if db=="Music":path=self.music_path
        elif db=="Music_Favorite":path=self.music_favorite_path
        elif db=="Videos":path=self.video_path
        elif db=="Videos_Family":path=self.video_family_path
        elif db=="Videos_Family":path=self.video_family_path
        elif db=="Videos_Music":path=self.video_music_path
        elif db=="Videos_Favorite":path=self.video_favorite_path
        elif db=="Videos_Karaoke":path=self.video_karaoke_path
        elif db=="Pictures":path=self.picture_path
        elif db=="Pictures_Family":path=self.picture_family_path
        elif db=="Pictures_Favorite":path=self.picture_favorite_path
        media={}
        with open(path, "w") as outfile:json.dump(media, outfile)
        outfile.close()
        if self.active_database==db:
            self.clear_all()
            if change:self.active_database=""
            self.write_setup()
    def add_files_to_db(self,db,files=None):
        music_exts=['*.mp3','*.wma','*.wav','*.mp2','*.ac3','*.aac','*.eac3','*.m4a',
                    '*.wmav1','*.wmav2','*.opus','*.ogg','*.aiff','*.alac','*.ape','*.flac']
        video_exts=['*.mp4','*.avi','*.mov','*.mkv','*.mpg','*.mpeg','*.wmv','*.webm','*.flv','*.mj2','*.3gp','*.3g2']
        image_exts=['*.bmp','*.jpg','*.jpeg','*.gif','*.png','*.ppm','*.dib']    
        if db=='Music':
            db_path=self.music_path
            exts=music_exts
        elif db=='Music_Favorite':
            db_path=self.music_favorite_path
            exts=music_exts
        elif db=='Videos':
            db_path=self.video_path    
            exts=video_exts
        elif db=='Videos_Family':
            db_path=self.video_family_path  
            exts=video_exts
        elif db=='Videos_Music':
            db_path=self.video_music_path  
            exts=video_exts
        elif db=='Videos_Favorite':
            db_path=self.video_favorite_path  
            exts=video_exts
        elif db=='Videos_Karaoke':
            db_path=self.video_karaoke_path   
            exts=video_exts
        elif db=='Pictures':
            db_path=self.picture_path    
            exts=image_exts
        elif db=='Pictures_Family':
            db_path=self.picture_family_path   
            exts=image_exts
        elif db=='Pictures_Favorite':
            db_path=self.picture_favorite_path
            exts=image_exts
        if files==None:
            files=filedialog.askopenfilenames(title=f"Please Select Files To Upload To {db} Database.", filetypes=(("Media files", exts),))
            if files=="" or files==None:return
        else:files=[files]
        temp_dict=json.load(open(db_path, "r+"))
        temp_list=[]
        for _, value in temp_dict.items():# Load List With temp_dict File Names 
            value=str(os.path.basename(value))
            temp_list.append(value)
        count=len(temp_dict)
        for _, name in enumerate(files):
            try:
                file_ext=os.path.splitext(name)[1].replace(".","*.")
                file_path=name[0].upper() + name[1:]# Make Sure Drive Letter Always Capitalized
                file_name=str(os.path.basename(file_path))
                if file_ext.lower() in exts:# Check For Duplicates Using Only File Name
                    c=Counter(temp_list)
                    duplicate=c[file_name]
                    if duplicate==0:
                        temp_list.append(file_name)
                        temp_dict[count]=file_path
                        count+=1
            except Exception:continue
        with open(db_path, "w") as outfile:json.dump(temp_dict, outfile)
        outfile.close()
        temp_dict.clear()
        temp_list.clear()
        if self.active_database==db:self.load_library(db)
    def upload_from_folder(self,db,ask=None):
        if db=='Music':
            exts=self.ffmpeg_audio_exts
            db_path=self.music_path
            init_dir=self.music_folder
        elif db=='Music_Favorite':
            exts=self.ffmpeg_audio_exts
            db_path=self.music_favorite_path
            init_dir=self.music_favorite_folder
        elif db=='Videos':
            exts=self.ffmpeg_video_exts
            db_path=self.video_path
            init_dir=self.video_folder    
        elif db=='Videos_Family':
            exts=self.ffmpeg_video_exts
            db_path=self.video_family_path  
            init_dir=self.video_family_folder    
        elif db=='Videos_Favorite':
            exts=self.ffmpeg_video_exts
            db_path=self.video_favorite_path  
            init_dir=self.video_favorite_folder
        elif db=='Videos_Karaoke':
            exts=self.ffmpeg_video_exts
            db_path=self.video_karaoke_path   
            init_dir=self.video_karaoke_folder    
        elif db=="Videos_Music":
            exts=self.ffmpeg_video_exts
            db_path=self.video_music_path
            init_dir=self.video_music_folder    
        elif db=='Pictures':
            exts=self.ffmpeg_image_exts
            db_path=self.picture_path    
            init_dir=self.picture_folder
        elif db=='Pictures_Family':
            exts=self.ffmpeg_image_exts
            db_path=self.picture_family_path   
            init_dir=self.picture_family_folder    
        elif db=='Pictures_Favorite':
            exts=self.ffmpeg_image_exts
            db_path=self.picture_favorite_path
            init_dir=self.picture_favorite_folder    
        else:return
        if ask==None:
            folder_path=filedialog.askdirectory(initialdir=init_dir,title=f"Please Select A Folder To Upload To {db} Database Or Click 'Select Folder' To Select Default Folder.")  
            if folder_path=="" or folder_path==None:return
        else:folder_path=init_dir    
        temp_dict=json.load(open(db_path, "r+"))
        temp_list=[]
        for _, value in temp_dict.items():# Load List With temp_dict File Names 
            value=str(os.path.basename(value))
            temp_list.append(value)
        count=len(temp_dict)
        for root, _, files in os.walk(folder_path):
            try:
                for _, name in enumerate(files):
                    folder_path=os.path.join(root, name).replace("\\","/")
                    file_ext=os.path.splitext(name)[1].replace(".","")
                    file_path=folder_path[0].upper() + folder_path[1:]# Make Sure Drive Letter Always Capitalized
                    file_name=str(os.path.basename(file_path))
                    if file_ext.lower() in exts:# Check For Duplicates Using Only File Name
                        c=Counter(temp_list)
                        duplicate=c[file_name]
                        if duplicate==0:
                            temp_list.append(file_name)
                            temp_dict[count]=file_path
                            count+=1
            except Exception:continue
        with open(db_path, "w") as outfile:json.dump(temp_dict, outfile)
        outfile.close()
        temp_dict.clear()
        temp_list.clear()
        if self.active_database==db or self.active_database=="":self.load_library(db)
    def update_devices(self,capture_devices: bool = False):# False For Playback Devices, True For Capture
        # Get a list of all audio devices
        mixer.init()# Only Use Pygame Mixer To Retrieve Audio Output Devices
        devices=[]
        output_devices=_sdl2.get_audio_device_names(capture_devices)
        mixer.quit()
        for d in output_devices:devices.append(d)
        self.device_menu.delete(0, 'end')
        for d in range(len(devices)):
            self.device_menu.add_command(label=devices[d],command=lambda x=devices[d]:self.select_output_device(x))
        self.device_menu.add_separator()
        self.device_menu.add_command(label="Refresh Device List",command=lambda:self.update_devices())
        root.update()
    def get_devices(self,capture_devices: bool = False):# False For Playback Devices, True For Capture
        # Get a list of all audio devices
        mixer.init()# Only Use Pygame Mixer To Retrieve Audio Output Devices
        devices=[]
        output_devices=_sdl2.get_audio_device_names(capture_devices)
        mixer.quit()
        for d in output_devices:devices.append(d)
        return devices
    def clear_all(self):# Destroys All Window Widgets
        try:
            self.media_list.delete(0,tk.END)
            self.Media_Dict.clear()
            self.Original_Dict.clear()
            root.update()
        except Exception:pass
    def write_setup(self):
        temp_dict={}
        sc=json.load(open(self.setup_path, "r"))
        json.dump(sc,open(self.setup_path, "w"),indent=4)
        temp_dict[0]=Screen_Height.get()
        temp_dict[1]=Screen_Position.get()
        temp_dict[2]=Slide_Show_Delay.get()
        temp_dict[3]=self.active_database
        with open(self.setup_path, "w") as outfile:json.dump(temp_dict, outfile)
        outfile.close()
        temp_dict.clear()
    def load_setup(self):
        temp_dict=json.load(open(self.setup_path, "r+"))
        if len(temp_dict)==0:
            hgt=int(screen_height-root_height)+int(0.2*taskbar_height)
            Screen_Height.set(hgt)
            Screen_Position.set("Top Center")
            temp_dict[0]=Screen_Height.get()
            temp_dict[1]=Screen_Position.get()
            if Slide_Show_Delay.get()=="":Slide_Show_Delay.set("0")
            temp_dict[2]=Slide_Show_Delay.get()
            temp_dict[3]=self.active_database
            with open(self.setup_path, "w") as outfile:json.dump(temp_dict, outfile)
            outfile.close()
            temp_dict.clear()
        else:    
            temp_dict[0]=Screen_Height.get()
            temp_dict[1]=Screen_Position.get()
            temp_dict[2]=Slide_Show_Delay.get()
            temp_dict[3]=self.active_database
            Screen_Height.set(temp_dict["0"])
            Screen_Position.set(temp_dict["1"])
            if Slide_Show_Delay.get()=="":Slide_Show_Delay.set("0")
            Slide_Show_Delay.set(temp_dict["2"])
            self.active_database=temp_dict["3"]
        root.update()
    def load_library(self,db,skip=None):
        if self.active_database=="" and db=="":return
        if skip==None:self.load_setup()
        if db=="Music":
            path=self.music_path
            self.active_media="music"
        elif db=="Music_Favorite":
            path=self.music_favorite_path
            self.active_media="music"
        elif db=="Videos":
            path=self.video_path
            self.active_media="video"
        elif db=="Videos_Family":
            path=self.video_family_path
            self.active_media="video"
        elif db=="Videos_Favorite":
            path=self.video_favorite_path
            self.active_media="video"
        elif db=="Videos_Music":
            path=self.video_music_path
            self.active_media="video"
        elif db=="Videos_Karaoke":
            path=self.video_karaoke_path
            self.active_media="video"
        elif db=="Pictures":
            path=self.picture_path
            self.active_media="picture"
        elif db=="Pictures_Family":
            path=self.picture_family_path
            self.active_media="picture"
        elif db=="Pictures_Favorite":
            path=self.picture_favorite_path
            self.active_media="picture"
        else:return    
        self.clear_all()
        self.Original_Dict=json.load(open(path, "r+"))
        self.Media_Dict=json.load(open(path, "r+"))
        if len(self.Media_Dict)==0:
            self.key_now=None
            msg1=f'{db.replace("_"," ")} Library Is Empty! Please Select\n'
            msg2='"Upload Folder Or File/s To Library" First.'
            msg=msg1+msg2
            messagebox.showwarning(f"<{db.replace("_"," ")} Library>",msg)
            return
        else:
            self.active_database=db
            root.title(f"My Media Player 5.8 ({db.replace("_"," ")} Library), Playing On Audio Device: {self.Active_Device}")
            if self.shuffled and not self.repeat:
                temp=list(self.Media_Dict.values())
                self.media_list
                random.shuffle(temp)
                self.Media_Dict=dict(zip(self.Media_Dict, temp))
            elif not self.shuffled:    
                temp=list(self.Original_Dict.values())
                self.Media_Dict=dict(zip(self.Original_Dict, temp))
            for key,self.file in self.Media_Dict.items():
                basename=os.path.basename(self.Media_Dict[key])
                text=os.path.splitext(basename)[0]
                index=f"{int(key)+1}.  {text}" 
                self.media_list.insert(tk.END,index)
            self.media_list.bind("<ButtonRelease>",lambda event:self.ctrl_btn_clicked(event,"media play"))
            self.vbar.config(command=self.media_list.yview )  
            self.ybar.config(command=self.media_list.xview ) 
            self.media_list.yview_moveto(0)     
        root.update()
    def select_output_device(self,device):
        try:
            devices=self.get_devices()# Quit Mixer
            result=list(filter(lambda x: device in x, devices))
            self.Active_Device=result[0]
            soundview_device=self.Active_Device.split("(", 1)[0].replace(" ","")
            if os.path.isfile(soundview_path):
                cmd=[soundview_path, "/SetDefault", soundview_device, "1", "/Unmute", soundview_device, "/SetVolume", soundview_device, str(Level.get())]
                subprocess.run(cmd, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            devices=AudioUtilities.GetSpeakers()# Initialize Master Volumn Slider
            self.interface=devices.Activate(IAudioEndpointVolume._iid_, CLSCTX_ALL, None)
            self.Master_Volume=cast(self.interface, POINTER(IAudioEndpointVolume))
            Level.set(5)
            self.Master_Volume.SetMasterVolumeLevelScalar(Level.get()/ 100, None)
            root.title(f"My Media Player 5.8 ({self.active_database.replace("_"," ")} Library), Playing On Audio Device: {self.Active_Device}")
        except Exception as ex:
            title='<Audio Output Device>'
            msg1='Initialization Audio Device Failed. Ending Program!\n'
            msg2=f"Error: '{ex}'"
            msg3="Using Default Audio Device."
            messagebox.showerror(title, msg1+msg2+msg3)
            pass
class AudioService:
    def __init__(self, url: str):
        self.url = url
    def get_audio_streams(video: YouTube):
        # Function to get audio streams from a video.
        return video.streams.filter(only_audio=True).order_by('mime_type').first()
class VideoService:
    def __init__(self, url: str, quality: str, path: str):
        self.url = url
        self.quality = quality
        self.path = path
    def update_progressbar(self, stream: Stream, chunk: bytes, bytes_remaining: int) -> None:
        filesize = stream.filesize
        bytes_received = filesize - bytes_remaining
        percent = round(100.0 * bytes_received / float(filesize), 1)
        progress_bar["value"]=percent
        root.update()
    def search_process(self) -> YouTube:
        # Performs the video search process.Returns An instance of the YouTube class representing the searched video. 
        try:
            video = YouTube(self.url,use_oauth=True,allow_oauth_cache=True,on_progress_callback=self.update_progressbar)
            return video
        except Exception as e:
            return False
    def get_available_resolutions(self, video: YouTube) -> set:
        try:
            # Get a set of all available resolutions for the video.
            streams = video.streams
            available_streams = streams.filter(
                progressive=False, adaptive=True, mime_type="video/mp4")
            audio_stream = streams.filter(only_audio=True).order_by('mime_type').first()
            resolutions_with_sizes = self.get_video_resolutions_sizes(available_streams, audio_stream)
            resolutions_with_sizes = sorted(
                resolutions_with_sizes, key=lambda x: int(
                    x[0][:-1]) if x[0][:-1].isdigit() else float('inf')
            )
            resolutions, sizes = zip(*resolutions_with_sizes)
            resolutions = list(resolutions)
            sizes = list(sizes)
            return resolutions, sizes, available_streams, audio_stream
        except Exception as e:
            title='<get_available_resolutions()>'
            msg1='get_available_resolutions() Failed!\n'
            msg2=f"Error: '{e}'"
            messagebox.showerror(title, msg1+msg2)
            return False
    def get_video_streams(self, quality: str, streams: YouTube.streams) -> YouTube:
        stream = streams.filter(res=quality).first()
        if quality.startswith(CANCEL_PREFIX):
            title='<get_video_streams>'
            msg1='VideoService.get_video_streams Failed!\n'
            msg2="No Stream Available For the URL."
            messagebox.showerror(title, msg1+msg2)
            return False
        if not stream:
            available_qualities = [stream.resolution for stream in streams]
            available_qualities = [int(res.replace("p", "")) for res in available_qualities]
            quality_int = int(quality.replace("p", "")) if "p" in quality else int(quality)
            selected_quality = min(available_qualities,key=lambda x: abs(quality_int - x))
            stream = streams.filter(res=str(selected_quality) + "p").first()
        return stream
    def get_selected_stream(self, video, is_audio: bool = False):
        resolutions, sizes,  streams, video_audio = self.get_available_resolutions(video)
        if not streams:
            title='<get_selected_stream>'
            msg1='VideoService.get_selected_stream Failed!\n'
            msg2="No Stream Available For the URL."
            messagebox.showerror(title, msg1+msg2)
            return False
        if not is_audio:
            self.quality = self.quality or ask_resolution(resolutions, sizes)
        if not self.quality or self.quality==CANCEL_PREFIX:
            Title.set("")
            return streams, video_audio, self.quality
        return streams, video_audio, self.quality
    def merging(self, video_name: str, audio_name: str):
        #Merges the video and audio files into a single file.
        output_directory = os.path.join(self.path, "output")
        os.makedirs(output_directory, exist_ok=True)
        base_name = os.path.splitext(os.path.basename(video_name))[0]
        output_file = os.path.join(output_directory, f"{base_name}.mp4")
        video_base_name = os.path.splitext(os.path.basename(video_name))[0]
        audio_base_name = os.path.splitext(os.path.basename(audio_name))[0]
        # Locate the video file
        video_path = None
        for file in os.listdir(self.path):
            if file.startswith(video_base_name):
                video_path = os.path.join(self.path, file)
                break
        if video_path is None:
            title='<merging>'
            msg1='VideoService.merging Failed!\n'
            msg2="Error Merging Audio And Video Files!"
            messagebox.showerror(title, msg1+msg2)
            return False
        # Locate the audio file
        audio_path = None
        for file in os.listdir(self.path):
            if file.startswith(audio_base_name):
                audio_path = os.path.join(self.path, file)
                break
        if audio_path is None:
            title='<merging>'
            msg1='VideoService.merging Failed!\n'
            msg2="Audio File Not Found!"
            messagebox.showerror(title, msg1+msg2)
            return False
        try:
            # Merge video and audio
            ffmpeg_merge_video_audio(video_path,audio_path,output_file,logger=None)
            # Remove original files
            os.remove(video_path)
            os.remove(audio_path)
            # Move the merged file to the current directory
            if os.path.exists(output_file):
                merged_file_name = os.path.basename(output_file)
                parent_directory = os.path.dirname(output_directory)
                final_path = os.path.join(parent_directory, merged_file_name)
                os.replace(output_file, final_path)
                os.rmdir(output_directory)
            else:
                title='<merging>'
                msg1='VideoService.merging Failed!\n'
                msg2="Video File Not Found In Output Directory!"
                messagebox.showerror(title, msg1+msg2)
                return False
        except Exception as e:
            title='VideoService.merging>'
            msg1='merging Failed!\n'
            msg2=f"Error: '{e}'"
            messagebox.showerror(title, msg1+msg2)
            return False
    @staticmethod
    def get_video_resolutions_sizes(available_streams: list[YouTube],  audio_stream: YouTube):
        try:
            # Get the available video resolutions.
            if not available_streams:
                return []
            # Calculate the total audio file size in bytes
            audio_filesize = audio_stream.filesize
            resolutions_with_sizes = []
            one_mb = 1024 * 1024
            one_gb = one_mb * 1024
            for stream in available_streams:
                if stream.resolution:
                    # Calculate the total video file size including audio in bytes
                    video_filesize_bytes = stream.filesize
                    if not stream.is_progressive:
                        video_filesize_bytes += audio_filesize
                    # Convert the video file size to KB or MB dynamically
                    if video_filesize_bytes >= one_gb:
                        # If size is >= 1 GB
                        video_filesize = \
                            f"{video_filesize_bytes / (one_gb):.4f} GB"
                    elif video_filesize_bytes >= one_mb:
                        # If size is >= 1 MB
                        video_filesize = \
                            f"{video_filesize_bytes / (one_mb):.2f} MB"
                    else:
                        video_filesize = f"{video_filesize_bytes / 1024:.2f} KB"
                    resolutions_with_sizes.append(
                        (stream.resolution, video_filesize))
            return resolutions_with_sizes
        except Exception as e:
            title='get_video_resolutions_sizes()>'
            msg1='et_video_resolutions_sizes() Failed!\n'
            msg2=f"Error: '{e}'"
            messagebox.showerror(title, msg1+msg2)
            return False
class FileService:
    def safe_filename(self,s: str, max_length: int = 255):
        # Sanitize a string making it safe to use as a filename.
        # Characters in range 0-31 (0x00-0x1F) are not allowed in ntfs filenames.
        ntfs_characters = [chr(i) for i in range(31)]
        characters = [
            r'"',
            r"\#",
            r"\$",
            r"\%",
            r"'",
            r"\*",
            r"\,",
            r"\.",
            r"\/",
            r"\:",
            r'"',
            r"\;",
            r"\<",
            r"\>",
            r"\?",
            r"\\",
            r"\^",
            r"\|",
            r"\~",
            r"\\\\",
        ]
        pattern = "|".join(ntfs_characters + characters)
        regex = re.compile(pattern, re.UNICODE)
        filename = regex.sub("", s)
        return filename[:max_length].rsplit(" ", 0)[0]
    def save_file(self, video: YouTube, filename: str, path: str):
        # Save the file to the specified path with the given filename.
        video.download(output_path=path, filename=filename)
    def generate_filename(self, video, video_id, is_audio=False, filename: str = ""):
        # Generate a filename for the downloaded video.
        file_type = 'audio' if is_audio else video.resolution
        extension = '.m4a' if is_audio else f".{video.mime_type.split('/')[1]}"
        title = filename if filename != "" else video.default_filename.split('.')[0]
        title = self.safe_filename(title)
        return f"{title}_{file_type}{extension}"
    def handle_existing_file(
            self, video: YouTube, video_id: str, filename: str, path: str, is_audio: bool = False):
        # Handle the case where a file with the same name already exists in path.
        if not self.is_file_exists(path, filename):
            return filename,False
        else:
            msg1=f"The File {filename} Already Exist!\n"
            msg2="Please Rename This File."
            msg=msg1+msg2
            new_filename=my_askstring("File Already Exist!", msg, filename)
        return new_filename,True
    @staticmethod
    def is_file_exists(path: str, filename: str):
        # Check if a file exists at the specified path and filename.
        return os.path.isfile(os.path.join(path, filename))
class DownloadService:
    def __init__(
            self, url: str, path: str, quality: str, is_audio: bool = False, make_playlist_in_order: bool = False):
        self.url = url
        self.path = path
        self.quality = quality
        self.is_audio = is_audio
        self.make_playlist_in_order = make_playlist_in_order
        self.video_service = VideoService(self.url, self.quality, self.path)# Instantize
        self.audio_service = AudioService(url)# Instantize
        self.file_service = FileService()# Instantize
    def get_json_num_keys(self):
        try:
            with open(shared_download_files, 'r') as file:
                    data = json.load(file)
                    return len(data.keys())
        except Exception:
            return None
    def download(self, title_number: int = 0):
        try:
            video, video_id, streams, video_audio, self.quality = self.preparing_download()
            if streams==CANCEL_PREFIX:return
            if self.is_audio:
                self.download_audio(video, video_audio, video_id, title_number)
            else:
                video_file = self.video_service.get_video_streams(self.quality, streams)
                if not video_file:raise Exception("Video File")
                self.download_video(video, video_id, video_file, video_audio, title_number)
            return True
        except Exception as e:
            title="DownloadService.download"
            msg1="Something Went Wrong While Downloading The Video!\n"
            msg2=f"Error: '{e}'\n"
            msg3="Ending Program!"
            msg=msg1+msg2+msg3
            messagebox.showerror(title, msg)
            destroy()
    def download_audio(self, video: YouTube, video_audio: YouTube, video_id: str, title_number: int = 0):
        audio_filename = self.file_service.generate_filename(video_audio, video_id, is_audio=True)
        base_name, extension = os.path.splitext(audio_filename)
        if self.make_playlist_in_order:
            audio_filename = f"{title_number}__{base_name}{extension}"
        if self.is_audio:    
            audio_filename, name_changed = self.file_service.handle_existing_file(
                video, video_id, audio_filename, self.path, self.is_audio)
        try:
            if self.is_audio:
                if not name_changed:
                    new_name=my_askstring("Rename Audio File","Rename The File Here If Desired ",base_name)
                    if new_name!=None and new_name!='':
                        base_name=new_name
                        audio_filename=f"{base_name}{extension}"
                    elif new_name==None:    
                        audio_filename=f"{base_name}{extension}"
                    elif new_name=='':
                        Title.set("")
                        return CANCEL_PREFIX   
                Title.set(audio_filename)
                root.update()    
                audio_filename, name_changed = self.file_service.handle_existing_file(
                    video, video_id, audio_filename, self.path, self.is_audio)
                if not audio_filename:return 
            self.file_service.save_file(video_audio, audio_filename,  self.path)
            # Clear Json File
            if self.is_audio:
                path_dict={}
                with open(shared_download_files, "w") as json_file:
                    json.dump(path_dict, json_file)
                json_file.close()
                # Write Download Path and Filename to Json file
                num_keys=self.get_json_num_keys()
                with open(shared_download_files, "w") as json_file:
                    path_dict[str(num_keys)]=self.path
                    path_dict[str(num_keys+1)]=audio_filename
                    json.dump(path_dict, json_file)
                json_file.close()
            return audio_filename
        except Exception as e:
            title="DownloadService.download_audio"
            msg1="Something Went Wrong While Downloading The Audio!\n"
            msg2=f"Error: '{e}'\n"
            msg3="Ending Program!"
            msg=msg1+msg2+msg3
            messagebox.showerror(title, msg)
            destroy()
    def download_video(self, video: YouTube, video_id: str, video_stream: YouTube, 
                       video_audio: YouTube, title_number: int = 0):
        # Generate filename with title, quality, and file extension
        video_filename = self.file_service.generate_filename(video_stream, video_id)
        video_base_name, video_extension = os.path.splitext(video_filename)
        # Prepend the title number and `__` to the filename if ordering is required
        if self.make_playlist_in_order:
            video_filename = f"{title_number}__{video_base_name}{video_extension}"
        new_name=my_askstring("Rename Video File","Rename The File Here If Desired ",video_base_name)
        if new_name!=None and new_name!='':
            video_base_name=new_name
            video_filename=f"{video_base_name}{video_extension}"
        elif new_name==None:    
            video_filename=f"{video_base_name}{video_extension}"
        elif new_name=='':
            Title.set("")
            return CANCEL_PREFIX   
        Title.set(video_filename)
        root.update()    
        # Handle existing files, Check For Duplicates
        video_filename,name_change = self.file_service.handle_existing_file(
            video, video_id, video_filename, self.path, self.is_audio)
        if not video_filename:return 
        try:
            self.file_service.save_file(video_stream, video_filename, self.path)
            audio_filename = self.download_audio(video, video_audio, video_id, title_number)
            video_base_name, video_extension = os.path.splitext(video_filename)
            audio_base_name, audio_extension = os.path.splitext(audio_filename)
            video_safe_filename = f"{self.file_service.safe_filename(video_base_name)}{video_extension}"
            audio_safe_filename = f"{self.file_service.safe_filename(audio_base_name)}{audio_extension}"

            self.video_service.merging(video_safe_filename, audio_safe_filename)
            # Write Download Path and Filename to Json file
            num_keys=self.get_json_num_keys()
            with open(shared_download_files, "w") as json_file:
                path_dict[str(num_keys)]=self.path
                path_dict[str(num_keys+1)]=video_filename
                json.dump(path_dict, json_file)
            json_file.close()
            return self.quality
        except Exception as e:
            title="DownloadService.download_video"
            msg1="Something Went Wrong While Downloading The Video!\n"
            msg2=f"Error: '{e}'\n"
            msg3="Ending Program!"
            msg=msg1+msg2+msg3
            messagebox.showerror(title, msg)
            destroy()
    def asking_video_or_audio(self):
        try:
            self.is_audio = asking_video_or_audio()
        except TypeError:
            return
        self.download()
    def preparing_download(self):#*
        video = self.video_service.search_process()
        if not video:
            title="< Preparing Download >"
            msg1="Something Went Wrong While Preparing The Download!\n"
            msg2="Ending Program!"
            msg=msg1+msg2
            messagebox.showerror(title, msg)
            return False, False,  False, False, False
        Title.set(video.title)
        root.update()
        video_id = video.video_id
        streams, video_audio, self.quality = self.video_service.get_selected_stream(video, self.is_audio)
        return video, video_id,  streams, video_audio, self.quality
class URLHandler:
    def __init__(self, url):
        self.url = url
    def validate_url(self):#*
        if self.__is_youtube_video_id(self.url):
            self.url = f"https://www.youtube.com/watch?v={self.url}"
        return self.validate_url_link(self.url)
    def validate_url_link(self, url: str):
        # Validates the given YouTube video URL.
        is_valid_link, link_type = self.__is_youtube_link(url)
        if not is_valid_link:
            return False, link_type.lower()
        return is_valid_link, link_type.lower()
    def __is_youtube_link(self, link: str):
        # Check if the given link is a YouTube video.
        is_video = self.__is_youtube_video(link)
        is_short = self.__is_youtube_shorts(link)
        return (is_video, "video") if is_video \
            else (is_short, "short") if is_short \
            else (False, "unknown")
    def __is_youtube_shorts(self, link: str):
        # Check if the given link is a YouTube shorts link.
        shorts_pattern = r"(?:https?:\/\/)?(?:www\.)?(?:youtube\.com\/(?:[^\/\n\s]+\/\S+\/|shorts\/|watch\?.*?v=))(?:(?:[^\/\n\s]+\/)?)([a-zA-Z0-9_-]+)"
        shorts_match = re.match(shorts_pattern, link)
        return bool(shorts_match)
    def __is_youtube_video(self, link: str):
        # Check if the given link is a YouTube video.
        video_pattern = re.compile(
            r"^(?:https?://)?(?:www\.)?(?:youtube(?:-nocookie)?\.com/(?:(watch\?v=|watch\?feature\=share\&v=)|embed/|v/|live_stream\?channel=|live\/)|youtu\.be/)([a-zA-Z0-9_-]{11})")
        return bool(video_pattern.match(link))
    def __is_youtube_video_id(self, video_id: str):
        # Check if the given string is a valid YouTube video ID.
        return len(video_id) == 11 and all(
            c in "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_-" for c in video_id)
    def not_valid_url(self, where):
        title=f'Validate {Download_Type.get()} URL '
        msg1=f'The {Download_Type.get()} URL Entered Is "Not Invalid"!\n'
        msg2='Please Entered A Valid YouTube URL!'
        msg=msg1+msg2
        messagebox.showerror(title, msg)
        URL.set("")
def ask_resolution(resolutions: set, sizes):
    try:
        # Prompts the user to choose a resolution for download
        size_resolution_mapping = dict(zip(resolutions, sizes))
        # Generate the choices for the user prompt
        resolution_choices = [
            f"{size} ~= {resolution}" for size, resolution in size_resolution_mapping.items()
        ] + [CANCEL_PREFIX]
        answer=my_askstring("Ask Resolution","Please Select A Resolution To Download",resolution_choices)
        if answer==None:return CANCEL_PREFIX
        # Extract the resolution part from the user's choice
        res=answer.split(" ~= ")[0]
        return res
    except Exception:
        return False
def change_download_type():#*
    Title.set("")
def change_download_folder(init_dir):#*
    folder_path=filedialog.askdirectory(initialdir=init_dir,title=f"Please Select A Folder For YouTube Downloads Or Click 'Select Folder' To Select Default Folder.")  
    if folder_path=="" or folder_path==None:return
    Download_Folder.set(folder_path)
    wid=len(Download_Folder.get())+1 
    YouTube_GUI.download_txt.config(width=wid)
    root.update()
def check_internet_connection(retry):#*
    try:
        requests.get("https://www.google.com", timeout=5)
        if retry:
            YouTube_GUI.retry_conn.destroy()
            YouTube_GUI.conn_results.config(text="  There is an Internet Connection  ",foreground="#ffffff",background="#369e09")
            YouTube_GUI.file_menu.entryconfig("Open YouTube", state="normal")
            root.update()
        return True
    except Exception:
        return False
def file_type():
    # Prompts the user to choose a file type for download and returns
    try:
        choices=['Audio', 'Video', CANCEL_PREFIX]
        answer=my_askstring("File Types","Choose The File Type You Want To Download",choices)
    except TypeError:
        return False
    except Exception as e:
        title="file_type"
        msg1="Something Went Wrong With file_type!\n"
        msg2=f"Error: '{e}'"
        msg=msg1+msg2
        messagebox.showerror(title, msg)
        return False
    return answer
def asking_video_or_audio():
    # Handles video link scenario.
    file_type_choice = file_type().lower()
    is_audio = file_type_choice.startswith("audio")
    if file_type_choice.startswith(CANCEL_PREFIX.lower()):
        Title.set("")
        title='asking_video_or_audio'
        msg='Cancelling the download!\n'
        messagebox.showerror(title, msg)
        return False
    return is_audio
def destroy():
    try:
        for widget in root.winfo_children():# Destroys Menu Bars, Frame, Scroll Bars etc...
            if isinstance(widget, tk.Canvas):widget.destroy()
            else:widget.destroy()
        os._exit(0)
    except Exception:
        pass
    os._exit(0)
def url_entry():
    if URL.get()!="":
        YouTube_GUI.fetch["state"]=NORMAL
def fetch_resolutions():
    VideoService.get_selected_stream(URL.get())
def open_youtube():
    if YouTube_GUI.file_menu.entrycget("Open YouTube", 'state')=="normal":
        subprocess.run(['start', 'https://www.youtube.com'], shell=True)
def enumWindowsProc(hwnd, lParam):
    if (lParam is None) or ((lParam is not None) and win32process.GetWindowThreadProcessId(hwnd)[1] == lParam):
        text = win32gui.GetWindowText(hwnd)
        if text:
            win32api.SendMessage(hwnd, win32con.WM_CLOSE)
class YouTube_GUI:
    def __init__(self):
        def main(url, path, audio_video):
            if not conn:return
            if audio_video=="Audio":
                audio=True
                video=False
            elif audio_video=="Video":
                audio=False
                video=True
            elif audio_video==CANCEL_PREFIX:return    
            if url is None or url=="":
                title="YouTube Downloader"
                msg1="Missing URL! Please\n"
                msg2="Enter A Valid  URL!"
                msg=msg1+msg2
                messagebox.showerror(title, msg)
                return
            Title.set("")
            progress_bar['value'] = 0
            download_complete.config(text="")
            root.update()
            url_handler = URLHandler(url)# Instantize
            is_valid_link, link_type = url_handler.validate_url()# Only Validates And Returns video link_type
            if not is_valid_link or link_type=='unknown':
                url_handler.not_valid_url('URL Link Type')
                return
            download_service = DownloadService(url, path, None)# Instantize
            if audio:
                download_service.is_audio = True
                video, video_id,  _, video_audio, _ = download_service.preparing_download()
                if not video or not video_id or not video_audio:
                    url_handler.not_valid_url('preparing_download()')
                    return
                response=download_service.download_audio(video, video_audio, video_id)
                if response==CANCEL_PREFIX:
                    Title.set("")
                    return
            elif video:
                show_busy_cursor()
                video, video_id, streams, video_audio, quality = download_service.preparing_download()
                hide_busy_cursor()
                if not video or not quality or not streams:
                    hide_busy_cursor()
                    url_handler.not_valid_url('preparing_download()')
                    return
                video_file = download_service.video_service.get_video_streams(quality, streams)
                response=download_service.download_video(video, video_id, video_file, video_audio)
            download_complete.config(text="Download Complete!")
            time.sleep(0.5)
            progress_bar["value"]=0
            title="Download Status"
            msg1="Your Download Has Completed And\n"
            msg2=f"Saved To {path}"
            msg=msg1+msg2
            messagebox.showinfo(title, msg)
            self.update()
        def hide_busy_cursor():
            self.config(cursor="")
        def show_busy_cursor():
            self.config(cursor="watch")
            self.update_idletasks()
        def open_youtube():
            if file_menu.entrycget("Open YouTube", 'state')=="normal":
                subprocess.run(['start', 'https://www.youtube.com'], shell=True)
        def open_readme():
            subprocess.Popen(["notepad.exe", youtube_readme])
        def enumWindowsProc(hwnd, lParam):
            if (lParam is None) or ((lParam is not None) and win32process.GetWindowThreadProcessId(hwnd)[1] == lParam):
                text = win32gui.GetWindowText(hwnd)
                if text:
                    win32api.SendMessage(hwnd, win32con.WM_CLOSE)
        def stop_app(app_exe):
            for process in psutil.process_iter():
                if process.name() == app_exe:
                    win32gui.EnumWindows(enumWindowsProc, process.pid)
        def close_open_browsers():
            try:
                # Get Installed Browsers
                browsers = ['chrome', 'firefox', 'edge', 'safari', 'opera', "brave", "DuckDuckGo"]
                # Check If Browser Is Open
                opened_browsers=[]
                for process in psutil.process_iter(['name']):
                    process_name = process.info['name']
                    for browser in browsers:
                        if browser in process_name:
                            opened_browsers.append(browser)
                # Close All Opened Browsers
                to_close = list(dict.fromkeys(opened_browsers))# Eliminate Duplicates
                for b in range(len(to_close)):
                    if to_close[b]=="chrome":
                        #self.stop_app("chrome.exe")
                        os.system("taskkill /f /im chrome.exe")
                    elif to_close[b]=="edge":      
                        os.system("taskkill /f /im msedge.exe")
                    elif to_close[b]=="firefox":      
                        stop_app("firefox.exe")
                    elif to_close[b]=="safari":      
                        stop_app("safari.exe")
                    elif to_close[b]=="opera":      
                        stop_app("opera.exe")
                    elif to_close[b]=="brave":      
                        stop_app("brave.exe")
                    elif to_close[b]=="DuckDuckGo":      
                        stop_app("DuckDuckGo.exe")
            except Exception:
                return
        def url_entry():
            if URL.get()!="":
                fetch["state"]=NORMAL
        def change_download_type():#*
            Title.set("")
        def change_download_folder(init_dir):#*
            folder_path=filedialog.askdirectory(initialdir=init_dir,title=f"Please Select A Folder For YouTube Downloads Or Click 'Select Folder' To Select Default Folder.")  
            if folder_path=="" or folder_path==None:return
            Download_Folder.set(folder_path)
            wid=len(Download_Folder.get())+1 
            download_txt.config(width=wid)
            self.update()
        def check_internet_connection(retry):#*
            try:
                requests.get("https://www.google.com", timeout=5)
                if retry:
                    retry_conn.destroy()
                    conn_results.config(text="  There is an Internet Connection  ",foreground="#ffffff",background="#369e09")
                    file_menu.entryconfig("Open YouTube", state="normal")
                    self.update()
                return True
            except Exception:
                return False
        def youtube_destroy():# X Icon Was Clicked
            for widget in self.winfo_children():
                if isinstance(widget, tk.Canvas):widget.destroy()
                else:widget.destroy()
            close_open_browsers()
            self.withdraw()
            root.deiconify()
            root.grab_set()
            root.focus_force()
            FF_Player.update_databases()
            root.update()
        self=Toplevel(root)# Displays The ratio Window
        root.withdraw()
        self.deiconify()
        self.grab_set() # Receive Events And Prevent root Window Interaction
        width=int(work_area[2]*0.6)
        height=int(work_area[3]*0.25)
        x=int((work_area[2]/2)-(width/2))
        y=int((work_area[3]/2)-(height/2))
        self.geometry('%dx%d+%d+%d' % (width, height, x, y, ))
        self.configure(bg="#094983")
        ReadMe_File=tk.StringVar()
        ReadMe_File.set(os.path.join(Path(__file__).parent.absolute(),"youtube_downloader_readme.txt"))
        youtube_readme=os.path.join(Path(__file__).parent.absolute(),"youtube_downloader_readme.txt")
        youtube_ico_path=os.path.join(Path(__file__).parent.absolute(),"youtube_downloads.ico")
        self.iconbitmap(youtube_ico_path)# root and children
        self.title("My YouTube GUI Downloader")
        self.resizable(True,True)
        self.protocol("WM_DELETE_WINDOW", youtube_destroy)
        self.update()
        # Widgets
        self.rowconfigure(9, minsize=30)
        self.columnconfigure(10, minsize=30)
        conn_lbl=tk.Label(self,text='Internet Connection: ',background="#094983",foreground="#ffffff",justify=RIGHT, anchor=E)
        conn_lbl.grid(row = 0, column = 0, sticky = E, pady = 2)
        conn=check_internet_connection(False)
        if conn:# Preceed
            text="  There is an Internet Connection  "
            forecolor="#ffffff"
            backcolor="#369e09"
        else:# Go No Further
            text="  No Internet Available! Check Your Connection And Try Again!  "
            forecolor="#f70505"
            backcolor="#ffffff"
        conn_results=tk.Label(self,text=text,background=backcolor,foreground=forecolor,justify="center",relief='solid')
        conn_results.grid(row = 0, column = 1, columnspan=2, sticky = W, pady = 3)
        if not conn:
            retry_conn=tk.Button(self,text="Retry Internet Connection",foreground="#ffffff",background="#094983",justify="center",anchor="w")
            retry_conn.grid(row = 0, column = 1, sticky = W, pady = 3)
            retry_conn.bind("<ButtonRelease>",lambda event:check_internet_connection(True))
        Download_Folder.set(str(os.path.join(Path.home(),"Downloads").replace("\\","/")))
        download_lbl=tk.Label(self,text='Select Destination Folder: ',background="#094983",foreground="#ffffff",justify="center",anchor=E)
        download_lbl.grid(row = 1, column = 0, columnspan=1 ,sticky = E, pady = 3)
        wid=len(Download_Folder.get())+1   
        download_txt=tk.Entry(self,textvariable=Download_Folder,background="#ffffff",foreground="#000000",justify="center",width=wid)
        download_txt.grid(row = 1, column = 1, columnspan=5, sticky = W, pady = 3)
        download_txt.bind("<ButtonRelease>",lambda event:change_download_folder(Download_Folder.get()))
        type_lbl=tk.Label(self,text='Select Download Type: ',background="#094983",foreground="#ffffff",justify="center",anchor=E)
        type_lbl.grid(row = 2, column = 0, columnspan=1, sticky = E, pady = 3)
        types=["Audio","Video","Cancel"]
        Download_Type.set(types[1])
        type_select=ttk.Combobox(self, textvariable=Download_Type, state="readonly")
        type_select['values'] = types
        type_select.grid(row = 2, column = 1, columnspan=1, sticky = W, pady = 3)
        type_select.bind("<<ComboboxSelected>>",lambda event:change_download_type())
        url_lbl=tk.Label(self,text='Enter YouTube URL: ',background="#094983",foreground="#ffffff",justify="center",anchor=E)
        url_lbl.grid(row = 3, column = 0, columnspan=1, sticky = E, pady = 3)
        URL=tk.StringVar()
        wid=int(width*0.05)
        url_txt=tk.Entry(self,textvariable=URL,background="#ffffff",foreground="#000000",justify="left", width=wid)
        url_txt.grid(row = 3, column = 1, columnspan=7, sticky = W, pady = 3)
        url_txt.bind("<KeyRelease>",lambda event:url_entry)
        fetch=tk.Button(self,text="Fetch Information",foreground="#ffffff",background="#094983",justify="center",anchor="center")
        fetch.grid(row = 3, column = 8, columnspan=2,sticky = W, pady = 3, padx=5)
        fetch.bind("<ButtonRelease>",lambda event:main(URL.get(),Download_Folder.get(),Download_Type.get()))
        title_lbl=tk.Label(self,text='Download Title: ',background="#094983",foreground="#ffffff",justify="center",anchor=E)
        title_lbl.grid(row = 4, column = 0, columnspan=1, sticky = E, pady = 3)
        self.update()
        title_width=url_txt.cget("width")
        Title=tk.StringVar()
        title_name=tk.Label(self,textvariable=Title,background="#ffffff",foreground="#000000",justify="center",anchor="w",width=title_width)
        title_name.grid(row = 4, column = 1, columnspan=8, sticky = W, pady = 3)
        if URL.get=="":fetch["state"] = DISABLED
        progress_lbl=tk.Label(self,text='Download Progress: ',background="#094983",foreground="#ffffff",justify="center")
        progress_lbl.grid(row = 5, column = 0, columnspan=1, sticky = E, pady = 3)
        self.update()
        p_length=(url_txt.winfo_width())
        global progress_bar
        style = Style()
        style.theme_use('clam') 
        style.configure("Horizontal.TProgressbar", troughcolor ='black', background='aqua')
        progress_bar = ttk.Progressbar(self,style="Horizontal.TProgressbar",orient=tk.HORIZONTAL, length=p_length,mode="determinate",max=100)
        progress_bar.grid(row = 5, column = 1, columnspan=6, sticky = W, pady = 6, ipady=6)
        download_complete=tk.Label(self,text="",background="#094983",foreground="#ffffff",justify="center",anchor="w")
        download_complete.grid(row = 5, column = 8 , columnspan=2, sticky = W, pady = 3, padx=5)
        menubar=Menu(self,fg="#000000")# Create Menubar
        file_menu=Menu(menubar,background='aqua',foreground='black',tearoff=0)
        menubar.add_cascade(label='            File',menu=file_menu)
        file_menu.add_command(label="Open YouTube",command=lambda:open_youtube())
        file_menu.add_separator()
        file_menu.add_command(label="Open Readme File",command=lambda:open_readme())
        file_menu.add_separator()
        file_menu.add_command(label="About",command=lambda:about())
        file_menu.add_separator()
        file_menu.add_command(label="Exit",command=lambda:youtube_destroy())
        self.config(menu=menubar)
        self.update()
        if conn:
            file_menu.entryconfig("Open YouTube", state="normal")
        else:file_menu.entryconfig("Open YouTube", state="disabled")
        # Clear Json File, json Object Used For Sharing Downloaded Files
        path_dict={}
        url_txt.focus_force()
        path_dict={}
        with open(shared_download_files, "w") as json_file:
            json.dump(path_dict, json_file)
        json_file.close()
        self.update()
        self.mainloop()
def my_askinteger(title,prompt,init_val,min_val,max_val):
    d=My_IntegerDialog(title, prompt ,init_val,min_val,max_val)
    answer=d.result
    root.update_idletasks()
    return answer  
class My_IntegerDialog(tk.simpledialog._QueryInteger):
    def body(self, master):
        self.attributes("-toolwindow", True)# Remove Min/Max Buttons
        self.bind('<KP_Enter>', self.ok)
        self.bind('<Return>', self.ok)
        pt=tk.Label(master, text=self.prompt, justify="left", font=media_font)
        pad=int((pt.winfo_reqwidth()/2)/2)
        pt.grid(row=2, padx=(5,5),pady=(5,5), sticky=W+E)
        self.entry=tk.Entry(master, name="entry", justify='center', bg="#d6ffff", font=media_font)
        self.entry.grid(row=3, padx=(pad,pad), sticky=W+E)
        self.entry.bind('<Map>', self.on_map)
        if self.initialvalue is not None:
            self.entry.insert(0, self.initialvalue)
            self.entry.select_range(0, END)
        root.update_idletasks()
        return self.entry
    def on_map(self, event):
        self.entry.focus_force()    
def set_slide_show():
    title="<Set Slide Show Delay Time In Seconds>"
    msg1='Note:The Edit Picture Menu Is Not Visible When Delay > 0!\n'
    msg2='Enter A Delay Time In Seconds For Picture Slide Show.\n'
    msg3='A Delay Time Of 0 Seconds Indicates No Slide Show.\n'
    msg4='Maximum Delay Time Is 120 Seconds.'
    msg=msg1+msg2+msg3+msg4
    delay=my_askinteger(title,msg,int(Slide_Show_Delay.get()),0,120)
    if delay!=None:
        Slide_Show_Delay.set(str(delay))
        FF_Player.write_setup()
def set_screen_size():
    title="<Set Screen Size For Media Window>"
    default=str((screen_height-root_height)+int(0.2*taskbar_height))
    msg1='Enter A Screen Height For Video Playback.\n'
    msg2=f"Default Screen Height For This Monitor = {default}.\n"
    msg3='Maximum Height For This Monitor is ' + str(work_area[3]) +' (Full Screen).\n'
    msg4='The Screen Width Will Be Determined By This Monitors Aspect Ratio!'
    msg=msg1+msg2+msg3+msg4
    hgt=my_askinteger(title,msg,Screen_Height.get(),100,work_area[3])
    if hgt!=None:
        Screen_Height.set(hgt)
        FF_Player.write_setup()
def my_askstring(title, prompt, init_val=None):
    d=My_StringDialog(title, prompt , init_val)
    answer=d.result
    root.update_idletasks()
    return answer  
class My_StringDialog(tk.simpledialog._QueryString):
    def body(self, master):# initialvalue May Be List, String Or None
        self.attributes("-toolwindow", True)# Remove Min/Max Buttons
        self.bind('<KP_Enter>', self.ok)
        self.bind('<Return>', self.ok)
        pt=tk.Label(master, text=self.prompt, justify="left", font=media_font)
        pad=int((pt.winfo_reqwidth()/2)/2)
        pt.grid(row=2, padx=(5,5),pady=(5,5), sticky=W+E)
        if self.initialvalue is not None:
            if type(self.initialvalue)==list:# List
                self.entry=ttk.Combobox(master, name="entry", state = "readonly",justify="center",font=media_font)
                self.entry['values']=self.initialvalue
                self.entry.current(0)
            else:# String
                wid=len(self.initialvalue)+2
                self.entry=tk.Entry(master, name="entry", justify='center', bg="#d6ffff",width=wid)
                self.entry.insert(0, self.initialvalue)
                self.entry.select_range(0, END)
        else:# None
            self.entry=tk.Entry(master, name="entry", justify='center', bg="#d6ffff", font=media_font)
            self.entry.insert(0, "")
            self.entry.select_range(0, END)
        self.entry.grid(row=3, padx=(pad,pad), sticky=W+E)
        self.entry.bind('<Map>', self.on_map)
        root.update_idletasks()
        return self.entry
    def on_map(self, event):
        self.entry.focus_force()    
def set_screen_position():
    title="<Set Screen Position For Media Window>"
    msg1='Select A Screen Position For Video Playback.\n'
    msg2='The Default Position Is ' + Screen_Position.get()+'.'
    msg=msg1+msg2
    positions=["Top Left","Top Center","Top Right","Center Left","Center","Center Right","Bottom Left","Bottom Center","Bottom Right"]
    pos=my_askstring(title,msg,positions)
    if pos!=None:
        Screen_Position.set(pos)
        FF_Player.write_setup()
def about():
    msg1='Creator: Ross Waters\nEmail: RossWatersjr@gmail.com\nLanguage: Python version 3.13.2 64-bit\n'
    msg2='Revision: 5.8\nRevision Date: 03/18/2025\nCreated For Windows 11'
    msg=msg1+msg2
    messagebox.showinfo('My Media Player', msg)
def get_key_press(event):
    print(f"You pressed: {event.keysym}")
    # Usage:  root.bind_all("<Key>", get_key_press)
def bind_keyboard():
    keys=['<KeyRelease-p>','<KeyRelease-P>','<KeyRelease-m>','<KeyRelease-M>','<KeyRelease-Right>','<KeyRelease-Left>',
            '<KeyRelease-Up>','<KeyRelease-Down>','<KeyRelease-f>','<KeyRelease-F>','<KeyRelease-q>','<KeyRelease-Q>',
            '<KeyRelease-w>','<KeyRelease-W>','<KeyRelease-e>','<KeyRelease-E>','<KeyRelease-r>','<KeyRelease-R>',
            '<KeyRelease-XF86AudioPlay>','<KeyRelease-XF86AudioPause>','<XF86AudioMute>','<KeyRelease-XF86AudioPrev>',
            '<KeyRelease-XF86AudioNext>','<KeyRelease-XF86AudioRaiseVolume>','<KeyRelease-XF86AudioLowerVolume>','<KeyRelease-Escape>']
    for k in range(len(keys)): 
        try:
            root.bind(keys[k], FF_Player.bound_keys)
        except Exception:
            continue
if __name__ == '__main__':
    root=tk.Tk()
    style=ttk.Style()
    style.theme_use('classic')
    style.map('TCombobox', background=[('readonly','#094983')])
    style.map('TCombobox', fieldbackground=[('readonly','#d4f2f2')])
    style.map('TCombobox', selectbackground=[('readonly','#0b5394')])
    style.map('TCombobox', selectforeground=[('readonly', '#ffffff')])
    style.configure("Vertical.TScrollbar", background="#094983")
    style.configure("Horizontal.TScrollbar", background="#094983")
    primary_monitor=MonitorFromPoint((0, 0))
    monitor_info=GetMonitorInfo(primary_monitor)
    monitor_area=monitor_info.get("Monitor")
    work_area=monitor_info.get("Work")
    aspect_ratio=work_area[2]/work_area[3]
    taskbar_height=monitor_area[3]-work_area[3]
    screen_height=work_area[3]-taskbar_height
    root_width=int(work_area[2]*0.8)
    root.wm_attributes("-topmost",True)
    root.configure(bg="#094983")
    root.resizable(False,False)
    size1=int(round((8*work_area[3])/1032))
    size2=int(round((12*work_area[3])/1032))
    size3=size2+4
    btn_hgt=int(round((30*work_area[3])/1032))
    lbl_hgt=int(round((20*work_area[3])/1032))
    media_font=font.Font(family='Times New Romans', size=size1, weight='normal', slant='italic')
    emoji_font=font.Font(family='Noto Emoji', size=size2, weight='normal', slant='roman')
    emoji_font2=font.Font(family='Noto Emoji', size=size3, weight='normal', slant='roman')
    soundview_path=os.path.join(Path(__file__).parent.absolute(), "SoundVolumeView.exe")
    shared_download_files=os.path.join(os.path.expanduser("~"),"youtube_downloads.json")# Store Folder And Song Title Here For Sharing
    Start_Time=DoubleVar()
    Level=IntVar()# Volume Meter
    Screen_Height=IntVar()
    Screen_Position=StringVar()
    Slide_Show_Delay=StringVar()
    Download_Folder=tk.StringVar()
    Download_Type=tk.StringVar()
    URL=tk.StringVar()
    Title=tk.StringVar()
    # Clear Json File, json Object Used For Sharing Downloaded Files
    path_dict={}
    FF_Player=FFPLAY(root)
    FF_Player.init_audio()
    root.protocol("WM_DELETE_WINDOW", FF_Player.destroy)
    title_skin=tk.PhotoImage(file=os.path.join(Path(__file__).parent.absolute(), '2560x100_dark.png'))
    btn_skin=tk.PhotoImage(file=os.path.join(Path(__file__).parent.absolute(), '500x100_dark.png'))
    main_frame=tk.Frame(root,relief="raised",borderwidth=5)
    main_frame.pack(side=TOP,anchor=NW,fill=X, expand=False, padx=(0,0), pady=(0,0))
    main_frame.config(bg="#0b5394")
    title_frame=tk.Frame(main_frame,relief="sunken",borderwidth=3)
    title_frame.pack(side=TOP,anchor=NW,fill=X, expand=True, padx=(3,3), pady=(3,3))
    title_frame.config(bg="#000000")
    pix_wid=int(root_width*0.17) #Make Width 17% Of Root Width
    volume_lbl=tk.Button(title_frame,text='Master Volume',image=btn_skin, compound="center",width=pix_wid+2,height=lbl_hgt,activeforeground='#4cffff',
                    background="#bcbcbc",foreground="#ffffff",font=media_font,justify="center",relief='sunken',borderwidth=5)
    volume_lbl.pack(side=LEFT,anchor=NW,fill=BOTH, expand=False, padx=(3,0), pady=(3,3))
    title_lbl=tk.Button(title_frame,text="",image=title_skin, compound="center",height=lbl_hgt,activeforeground='#4cffff',
                    background="#aeaeae",foreground="#ffffff",font=media_font,justify="center",relief='sunken',borderwidth=5)
    title_lbl.pack(side=RIGHT,anchor=NE,fill=BOTH,expand=True,padx=(5,3), pady=(3,3))
    slider_frame=tk.Frame(main_frame,relief="sunken",borderwidth=3)
    slider_frame.pack(side=TOP,anchor=NW,fill=BOTH, expand=False, padx=(3,3), pady=(0,3))
    slider_frame.config(bg="#000000")
    volume=tk.Scale(slider_frame, variable=Level, from_=0,to=100, orient='horizontal', resolution=1, 
                    tickinterval=50,showvalue=1,borderwidth=5,relief="sunken",font=media_font,
                    length=pix_wid,bg="#333333",fg="#ffffff",troughcolor="#001829", activebackground="#4cffff",
                    highlightthickness=3,command=lambda event:FF_Player.set_master_volume())
    volume.pack(side=LEFT,anchor=NW,fill=BOTH, expand=False, padx=(3,0), pady=(3,3))
    volume.bind("<ButtonRelease-1>",lambda event:FF_Player.slider_released())# Sets Video Window aboutctive
    time_scale=tk.Scale(slider_frame,relief="sunken",orient='horizontal',resolution=0,
                        bg="#333333",borderwidth=5,font=media_font,fg="#ffffff",troughcolor="#001829",  
                        activebackground="#4cffff",highlightthickness=3)
    time_scale.pack(side=LEFT,anchor=NW,fill=BOTH,expand=True, padx=(5,3), pady=(3,3))
    time_scale.bind("<ButtonRelease-1>",lambda event:FF_Player.end_seeking(event))
    time_scale.bind("<ButtonPress-1>",lambda event:FF_Player.begin_seeking(event))
    ctrl_frame=tk.Frame(main_frame,relief="sunken",borderwidth=3)
    ctrl_frame.pack(side=RIGHT,anchor=NE,fill=BOTH, expand=True, padx=(3,3), pady=(0,3))
    ctrl_frame.config(bg="#000000")
    quit_btn=tk.Button(ctrl_frame,text="Quit",foreground="#ffffff",image=btn_skin, compound="center",font=media_font,relief="sunken",
                       background="#bcbcbc",borderwidth=5,activeforeground="#4cffff",height=btn_hgt,width=1,justify="center",anchor="center")
    quit_btn.pack(side=RIGHT,fill=X, expand=True, padx=(5,3), pady=(3,3))
    quit_btn.bind("<ButtonRelease>",lambda event:FF_Player.destroy())
    stop_btn=tk.Button(ctrl_frame,text="⏹️",foreground="#ffffff",image=btn_skin, compound="center",font=emoji_font,relief="sunken",
                       background="#bcbcbc",borderwidth=5,activeforeground="#4cffff",height=btn_hgt,width=1,justify="center",anchor="center")
    stop_btn.pack(side=RIGHT,fill=X, expand=True, padx=(0,0), pady=(3,3))
    stop_btn.bind("<ButtonRelease>",lambda event:FF_Player.ctrl_btn_clicked(event,"stop"))
    mute_btn=tk.Button(ctrl_frame,text="\U0001F50A",foreground="#ffffff",image=btn_skin, compound="center",font=emoji_font2,relief="sunken",
                       background="#bcbcbc",borderwidth=5,activeforeground="#4cffff",height=btn_hgt,width=1,justify="center",anchor="center")
    mute_btn.pack(side=RIGHT,fill=X, expand=True, padx=(5,5), pady=(3,3))
    mute_btn.bind("<ButtonRelease>",lambda event:FF_Player.ctrl_btn_clicked(event,"mute"))
    repeat_btn=tk.Button(ctrl_frame,text="🔁",foreground="#ffffff",image=btn_skin, compound="center",font=emoji_font2,relief="sunken",
                       background="#bcbcbc",borderwidth=5,activeforeground="#4cffff",height=btn_hgt,width=1,justify="center",anchor="center")
    repeat_btn.pack(side=RIGHT,fill=X, expand=True, padx=(0,0), pady=(3,3))
    repeat_btn.bind("<ButtonRelease>",lambda event:FF_Player.ctrl_btn_clicked(event,"repeat"))
    pause_btn=tk.Button(ctrl_frame,text="⏸️",foreground="#ffffff",image=btn_skin, compound="center",font=emoji_font,relief="sunken",
                       background="#bcbcbc",borderwidth=5,activeforeground="#4cffff",height=btn_hgt,width=1,justify="center",anchor="center")
    pause_btn.pack(side=RIGHT,fill=X, expand=True, padx=(5,5), pady=(3,3))
    pause_btn.bind("<ButtonRelease>",lambda event:FF_Player.pause(event))
    next_btn=tk.Button(ctrl_frame,text="⏭️",foreground="#ffffff",image=btn_skin, compound="center",font=emoji_font,relief="sunken",
                       background="#bcbcbc",borderwidth=5,activeforeground="#4cffff",height=btn_hgt,width=1,justify="center",anchor="center")
    next_btn.pack(side=RIGHT,fill=X, expand=True, padx=(0,0), pady=(3,3))
    next_btn.bind("<ButtonRelease>",lambda event:FF_Player.ctrl_btn_clicked(event,"next"))
    previous_btn=tk.Button(ctrl_frame,text="⏮️",foreground="#ffffff",image=btn_skin, compound="center",font=emoji_font,relief="sunken",
                       background="#bcbcbc",borderwidth=5,activeforeground="#4cffff",height=btn_hgt,width=1,justify="center",anchor="center")
    previous_btn.pack(side=RIGHT,fill=X, expand=True, padx=(5,5), pady=(3,3))
    previous_btn.bind("<ButtonRelease>",lambda event:FF_Player.ctrl_btn_clicked(event,"previous"))
    shuffle_btn=tk.Button(ctrl_frame,text="🔀"+" ▶",foreground="#ffffff",image=btn_skin, compound="center",font=emoji_font2,relief="sunken",
                       background="#bcbcbc",borderwidth=5,activeforeground="#4cffff",height=btn_hgt,width=1,justify="center",anchor="center")
    shuffle_btn.pack(side=RIGHT,fill=X, expand=True, padx=(0,0), pady=(3,3))
    shuffle_btn.bind("<ButtonRelease>",lambda event:FF_Player.ctrl_btn_clicked(event,"shuffled"))
    play_btn=tk.Button(ctrl_frame,text="▶️",foreground="#ffffff",image=btn_skin, compound="center",font=emoji_font,relief="sunken",
                       background="#bcbcbc",borderwidth=5,activeforeground="#4cffff",height=btn_hgt,width=1,justify="center",anchor="center")
    play_btn.pack(side=RIGHT,fill=X, expand=True, padx=(3,5), pady=(3,3))
    play_btn.bind("<ButtonRelease>",lambda event:FF_Player.ctrl_btn_clicked(event,"btn play"))
    FF_Player.load_menubar()
    root_height=main_frame.winfo_reqheight()
    x=(work_area[2]/2)-(root_width/2)
    root_x=int(x-((7/x)*x))# x Not Exactly Centered, Use Correction Factor
    root_y=screen_height-root_height
    root.geometry('%dx%d+%d+%d' % (root_width, root_height, root_x, root_y, ))
    ico_path=os.path.join(Path(__file__).parent.absolute(),"movie.ico")
    root.iconbitmap(ico_path)
    root.title("My Media Player 5.8")
    bind_keyboard()
    FF_Player.load_setup()
    root.after(50, FF_Player.load_library(FF_Player.active_database,True))    
    root.mainloop()
