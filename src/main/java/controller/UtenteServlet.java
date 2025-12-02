package controller;

import model.beans.Utente;
import services.UtenteService;

import javax.servlet.RequestDispatcher;
import javax.servlet.ServletException;
import javax.servlet.annotation.WebServlet;
import javax.servlet.http.HttpServlet;
import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;
import java.io.IOException;
import java.sql.SQLException;

@WebServlet(name = "UtenteServlet", value = "/UtenteServlet")
public class UtenteServlet extends HttpServlet {
    private UtenteService utenteService;

    @Override
    public void init() throws ServletException {
        try {
            this.utenteService = new UtenteService();
        } catch (SQLException e) {
            throw new ServletException("Failed to initialize UtenteService", e);
        }
    }

    @Override
    protected void doGet(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
        try {
            Utente utente = utenteService.getUtenteById(Integer.parseInt(request.getParameter("utente")));
            request.setAttribute("utente", utente);

            String address = "/paginaUtente.jsp";
            RequestDispatcher dispatcher = request.getRequestDispatcher(address);
            dispatcher.forward(request, response);
        } catch (SQLException e) {
            e.printStackTrace();
            response.sendError(HttpServletResponse.SC_INTERNAL_SERVER_ERROR);
        }
    }

    @Override
    protected void doPost(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
        doGet(request, response);
    }
}

