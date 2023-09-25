FROM pytorch/pytorch:latest

RUN apt-get update && \
    DEBIAN_FRONTEND=noninteractive apt-get install -y git htop atop graphviz && \
    apt-get clean && \
    rm -rf /var/lib/apt/lists/*

RUN pip install --upgrade pip

COPY . /workspace

WORKDIR /workspace

RUN pip install -r requirements.txt

EXPOSE 8888

CMD ["jupyter", "notebook", "--ip='0.0.0.0'", "--port=8888", "--no-browser", "--allow-root", "--NotebookApp.token=''"]
